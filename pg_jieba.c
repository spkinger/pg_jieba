/*-------------------------------------------------------------------------
 *
 * pg_jieba.c
 *    a text search parser for Chinese
 *
 * Author: Jaimin Pan <jaimin.pan@gmail.com>
 *
 * IDENTIFICATION
 *    pg_jieba.cpp
 *
 *-------------------------------------------------------------------------
 */

/* 系统标准头文件 */
#include <signal.h>      /* 用于 SIGHUP 信号处理 */
#include <limits.h>      /* 用于 UINT32_MAX */
#include <sys/types.h>   /* 用于 kill() */
#include <unistd.h>      /* 添加此行以声明 unlink 函数 */

/* PostgreSQL 核心头文件 */
#include "postgres.h"    /* PostgreSQL 核心头文件 */
#include "miscadmin.h"   /* 用于 PostmasterPid */
#include "fmgr.h"       /* 用于 PG_MODULE_MAGIC */
#include "executor/spi.h"  /* 用于 SPI 接口 */

/* PostgreSQL 存储相关头文件 */
#include "storage/ipc.h"        /* 用于共享内存操作 */
#include "storage/shmem.h"      /* 用于共享内存操作 */
#include "storage/lwlock.h"     /* 用于轻量级锁 */

/* PostgreSQL 工具类头文件 */
#include "lib/stringinfo.h"     /* 用于字符串处理 */
#include "utils/guc.h"          /* 用于GUC变量 */
#include "utils/elog.h"         /* 用于日志记录 */
#include "tsearch/ts_public.h"  /* 用于全文检索 */
#include "libpq/auth.h"         /* 用于 ClientAuthentication_hook */
#include "utils/varlena.h"      /* 用于 varlena 类型 */
#include "utils/builtins.h"     /* 用于 quote_identifier 函数 */

/* 项目自定义头文件 */
#include "jieba.h"

PG_MODULE_MAGIC;

/* Start From 1 and LASTNUM is the last number */
int LASTNUM = sizeof(lex_descr) / sizeof(lex_descr[0]) - 1;

/*
 * types
 */
typedef struct
{
	char	   *buffer;			/* text to parse */
	int			len;			/* length of the text in buffer */
	JiebaCtx   *ctx;
	ParStat    *stat;
} ParserState;

/* 共享内存存储字典版本号 */
typedef struct
{
    LWLock *lock;
    uint32 global_version;
} SharedDictionaryState;

/* SharedDictionaryState占用共享内存大小计算函数 */
static Size pg_jieba_shmem_size(void);

/* 保存之前钩子的变量，共享内存相关 */
static shmem_startup_hook_type prev_shmem_startup_hook = NULL;
static shmem_request_hook_type prev_shmem_request_hook = NULL;

static void init_shared_memory(void);
static void pg_jieba_shmem_request(void);

void _PG_init(void);
void _PG_fini(void);

/*
 * prototypes
 */
PG_FUNCTION_INFO_V1(jieba_start);
Datum jieba_start(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(jieba_query_start);
Datum jieba_query_start(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(jieba_mp_start);
Datum jieba_mp_start(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(jieba_hmm_start);
Datum jieba_hmm_start(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(jieba_gettoken);
Datum jieba_gettoken(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(jieba_end);
Datum jieba_end(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(jieba_lextype);
Datum jieba_lextype(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(jieba_reload_dict);
Datum jieba_reload_dict(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(jieba_dict_add_table);
Datum jieba_dict_add_table(PG_FUNCTION_ARGS);

PG_FUNCTION_INFO_V1(jieba_dict_remove_table);
Datum jieba_dict_remove_table(PG_FUNCTION_ARGS);

#define DICT_EXT "dict"
#define MODEL_EXT "model"

static void DefineCustomConfigVariables(void);
static void recompute_dicts_path(void);
static char* extract_dict_list(const char *dictsString);
static char* extract_data_path_dict_list(const char *dictsString, const char *userDictsString);
static char* jieba_get_tsearch_config_filename(const char *basename, const char *extension);
static char* jieba_get_data_path_dict_filename(const char *basename, const char *extension);
/* 添加信号处理函数声明 */
static void pg_jieba_sighup_handler(SIGNAL_ARGS);
/* 保存之前的 SIGHUP 处理函数 */
static void (*prev_sighup_handler) (SIGNAL_ARGS) = NULL;
/* 添加信号处理函数声明 */
static void pg_jieba_backend_sighup_handler(SIGNAL_ARGS);
/* 保存之前的 SIGHUP 处理函数 */
static void (*prev_sighup_handler_backend) (SIGNAL_ARGS) = NULL;
/* 保存原始的 ClientAuthentication_hook */
static ClientAuthentication_hook_type prev_ClientAuthentication = NULL;
/* 登录成功后注册信号处理器 */
static void jieba_client_authentication(Port *port, int status);
/* 检测刷新字典 */
static void check_and_refresh_dictionary(void);
/* 更新字典版本号，并通知Postmaster刷新字典 */
static void jieba_reload_dict_common(void);
/* 修改参数：pg_jieba.data_path_user_dict */
static void edit_data_path_user_dict(const char *conf_val);

static JiebaCtx* jieba = NULL;

/* GUC variables */
static char *pg_jieba_hmm_model = "jieba_hmm";
static char *pg_jieba_dict = "jieba_base";
static char *pg_jieba_user_dict = "jieba_user";
static char *pg_jieba_data_path_user_dict = NULL;

/* These variables are the values last set */
// static char *userDicts = NULL; /* not used */

/* The above values are valid only if userDictsValid */
static bool userDictsValid = true;

static bool check_user_dict(char **newval, void **extra, GucSource source);
static void assign_user_dict(const char *newval, void *extra);

static bool check_data_path_user_dict(char **newval, void **extra, GucSource source);
static void assign_data_path_user_dict(const char *newval, void *extra);

static SharedDictionaryState *shared_state = NULL;
static uint32 local_version = 0; /* 每个进程的本地版本号 */


/*
 * Module load callback
 */
void
_PG_init(void)
{
	if (!process_shared_preload_libraries_in_progress)
	{
		ereport(LOG,
				(errmsg("pg_jieba Extension is not loaded by shared_preload_libraries, "
						"Variables can't be configured")));
	}
	else
	{
		DefineCustomConfigVariables();
	}

	/* 保存之前的钩子并设置新的钩子 */
	prev_shmem_request_hook = shmem_request_hook;
	shmem_request_hook = pg_jieba_shmem_request;
	
	prev_shmem_startup_hook = shmem_startup_hook;
	shmem_startup_hook = init_shared_memory;

	/* 替换 ClientAuthentication_hook */
	prev_ClientAuthentication = ClientAuthentication_hook;
	ClientAuthentication_hook = jieba_client_authentication;

	prev_sighup_handler = pqsignal(SIGHUP, pg_jieba_sighup_handler);

	userDictsValid = false;
	recompute_dicts_path();
}

/*
 * Module unload callback
 */
void
_PG_fini(void)
{
	if (jieba) {
		Jieba_Free(jieba);
		jieba = NULL;
	}

	/* 恢复之前的钩子 */
	shmem_request_hook = prev_shmem_request_hook;
	shmem_startup_hook = prev_shmem_startup_hook;
	ClientAuthentication_hook = prev_ClientAuthentication;

	/* 不再指向共享内存 */
	if (shared_state)
	{
		shared_state = NULL;
	}
}

/*
 * 初始化共享内存
 */
void
init_shared_memory(void)
{
	bool found;

	LWLockAcquire(AddinShmemInitLock, LW_EXCLUSIVE);

	/* 分配共享内存 */
	shared_state = ShmemInitStruct("SharedDictionaryState",
								  sizeof(SharedDictionaryState),
								  &found);

	if (!found)
	{
		/* 首次初始化 */
		shared_state->lock = &(GetNamedLWLockTranche("pg_jieba_shared_lock"))->lock;
		shared_state->global_version = 0;
	}

	LWLockRelease(AddinShmemInitLock);

	elog(LOG, "pg_jieba: Shared dictionary state initialized");

	/* 调用之前的钩子（如果存在） */
	if (prev_shmem_startup_hook)
		prev_shmem_startup_hook();
}

/*
 * functions
 */
Datum
jieba_start(PG_FUNCTION_ARGS)
{
	ParserState* const pst = (ParserState *) palloc0(sizeof(ParserState));
	pst->buffer = (char *) PG_GETARG_POINTER(0);
	pst->len = PG_GETARG_INT32(1);

	pst->ctx = jieba;

	pst->stat = Jieba_Cut(pst->ctx, pst->buffer, pst->len, MODE_MIX);

	PG_RETURN_POINTER(pst);
}

Datum
jieba_query_start(PG_FUNCTION_ARGS)
{
	ParserState* const pst = (ParserState *) palloc0(sizeof(ParserState));
	pst->buffer = (char *) PG_GETARG_POINTER(0);
	pst->len = PG_GETARG_INT32(1);

	pst->ctx = jieba;

	pst->stat = Jieba_Cut(pst->ctx, pst->buffer, pst->len, MODE_QRY);

	PG_RETURN_POINTER(pst);
}

Datum
jieba_mp_start(PG_FUNCTION_ARGS)
{
	ParserState* const pst = (ParserState *) palloc0(sizeof(ParserState));
	pst->buffer = (char *) PG_GETARG_POINTER(0);
	pst->len = PG_GETARG_INT32(1);

	pst->ctx = jieba;

	pst->stat = Jieba_Cut(pst->ctx, pst->buffer, pst->len, MODE_MP);

	PG_RETURN_POINTER(pst);
}

Datum
jieba_hmm_start(PG_FUNCTION_ARGS)
{
	ParserState* const pst = (ParserState *) palloc0(sizeof(ParserState));
	pst->buffer = (char *) PG_GETARG_POINTER(0);
	pst->len = PG_GETARG_INT32(1);

	pst->ctx = jieba;

	pst->stat = Jieba_Cut(pst->ctx, pst->buffer, pst->len, MODE_HMM);

	PG_RETURN_POINTER(pst);
}

Datum
jieba_gettoken(PG_FUNCTION_ARGS)
{
	ParserState* const pst = (ParserState *) PG_GETARG_POINTER(0);
	char	  **t = (char **) PG_GETARG_POINTER(1);
	int		   *tlen = (int *) PG_GETARG_POINTER(2);
	int			type = -1;

	JiebaResult* curr = Jieba_GetNext(pst->ctx, pst->stat);

	/* already done the work, or no sentence */
	if (curr == NULL)
	{
		*tlen = 0;
		type = 0;

		PG_RETURN_INT32(type);
	}

	type = curr->attr;
	*tlen = curr->len;
	*t = curr->str;

	PG_RETURN_INT32(type);
}

Datum
jieba_end(PG_FUNCTION_ARGS)
{
	ParserState *pst = (ParserState *) PG_GETARG_POINTER(0);

	if (pst->stat) {
		ParStat_Free(pst->stat);
		pst->stat = NULL;
	}

	pfree(pst);
	PG_RETURN_VOID();
}

Datum
jieba_lextype(PG_FUNCTION_ARGS)
{
	int			i;
	int			size = LASTNUM;
	LexDescr   *descr = (LexDescr *) palloc(sizeof(LexDescr) * (size + 1));

	for (i = 1; i <= size; i++)
	{
		descr[i - 1].lexid = i;
		descr[i - 1].alias = pstrdup(lex_descr[i].token);
		descr[i - 1].descr = pstrdup(lex_descr[i].descr);
	}

	descr[size].lexid = 0;

	PG_RETURN_POINTER(descr);
}

Datum
jieba_reload_dict(PG_FUNCTION_ARGS)
{
	jieba_reload_dict_common();
	PG_RETURN_VOID();
}

Datum
jieba_dict_add_table(PG_FUNCTION_ARGS)
{
    text *table_name_text;
    char *table_name;
    const char *quoted_table_name;
    StringInfoData query;
    SPITupleTable *tuptable;
    TupleDesc tupdesc;
    int ret, rows;
    FILE *fp;
    char* dict_path;
    StringInfoData buf;
    List *dict_name_list;
    ListCell *lc;
    bool found = false;
    FILE *conf_file;
    char conf_path[MAXPGPATH];
	char *local_data_path_user_dict = NULL;
	char *data_path_user_dict_copy;

	// 利用共享内存锁来防止并发操作
	LWLockAcquire(shared_state->lock, LW_EXCLUSIVE);
	// ---------------查询用户指定的词典表收集数据---------------
    // 从参数中接收表名
    table_name_text = PG_GETARG_TEXT_PP(0);
    table_name = text_to_cstring(table_name_text);
    quoted_table_name = quote_identifier(table_name);
    
    // 连接 SPI
    if (SPI_connect() != SPI_OK_CONNECT)
        ereport(ERROR, (errcode(ERRCODE_INTERNAL_ERROR), errmsg("pg_jieba: SPI_connect failed")));

    // 构建查询语句
    initStringInfo(&query);
    appendStringInfo(&query, "SELECT word, weight, tag FROM %s", quoted_table_name);

    // 执行查询
    ret = SPI_execute(query.data, true, 0);
    if (ret != SPI_OK_SELECT)
        ereport(ERROR, (errcode(ERRCODE_INTERNAL_ERROR), errmsg("pg_jieba: SPI_execute failed: error code %d", ret)));

    // 获取结果
    rows = SPI_processed;
    tuptable = SPI_tuptable;
    tupdesc = tuptable->tupdesc;

	// ---------------将查询结果写入 表名.dict 文件---------------
    // 打开 jieba_user.dict 文件
    dict_path = jieba_get_data_path_dict_filename(table_name, DICT_EXT);
    fp = fopen(dict_path, "w");
    if (fp == NULL)
    {
        SPI_finish();
        ereport(ERROR, (errcode_for_file_access(), errmsg("pg_jieba: could not open user dictionary file: %m")));
    }

    // 将查询结果写入 表名.dict 文件
    for (int i = 0; i < rows; i++)
    {
        HeapTuple tuple = tuptable->vals[i];
        char *word = SPI_getvalue(tuple, tupdesc, 1);
        char *weight = SPI_getvalue(tuple, tupdesc, 2);
        char *tag = SPI_getvalue(tuple, tupdesc, 3);

        if (weight && tag)
        {
            fprintf(fp, "%s %s %s\n", word, weight, tag);
        }
        else if (weight)
        {
            fprintf(fp, "%s %s\n", word, weight);
        }
        else
        {
            fprintf(fp, "%s\n", word);
        }

        if (word) pfree(word);
        if (weight) pfree(weight);
        if (tag) pfree(tag);
    }

    // 关闭文件和 SPI 连接
    fclose(fp);
    SPI_finish();
	elog(LOG, "pg_jieba: user dictionary export to %s", dict_path);
	// ---------------将新词典文件名追加到 pg_jieba.data_path_user_dict 中---------------
	if (pg_jieba_data_path_user_dict && pg_jieba_data_path_user_dict[0] != '\0')
	{
		// 使用 ',' 作为分隔符
		data_path_user_dict_copy = pstrdup(pg_jieba_data_path_user_dict);
		if (!SplitIdentifierString(data_path_user_dict_copy, ',', &dict_name_list))
			ereport(ERROR, (errcode(ERRCODE_SYNTAX_ERROR), errmsg("pg_jieba: split dict_name_list failed")));

		// 判断列表中是否存在相同的table_name
		foreach(lc, dict_name_list)
		{
			const char *dict_name = (const char *) lfirst(lc);
			if (strcmp(dict_name, table_name) == 0)
			{
				found = true;
				break;
			}
		}

		elog(LOG, "pg_jieba: pg_jieba_data_path_user_dict='%s' 111111 found=%d", pg_jieba_data_path_user_dict, found);
		// 如果不存在相同的table_name，追加
		if (!found)
		{
			initStringInfo(&buf);
			appendStringInfo(&buf, "%s,%s", pg_jieba_data_path_user_dict, table_name);
			edit_data_path_user_dict(buf.data);
			pfree(buf.data);
		}

		if (dict_name_list) {
			list_free(dict_name_list);
		}
		if (data_path_user_dict_copy) {
			pfree(data_path_user_dict_copy);
		}
	}
	else
	{
		edit_data_path_user_dict(table_name);
	}
	// ---------------保存 pg_jieba.data_path_user_dict 到 data_directory 目录下的 jieba.conf 中---------------
	if (pg_jieba_data_path_user_dict)
	{
		snprintf(conf_path, MAXPGPATH, "%s/jieba.conf", DataDir);
		conf_file = fopen(conf_path, "w");
		if (conf_file == NULL)
		{
			ereport(ERROR, (errcode(ERRCODE_IO_ERROR), errmsg("无法打开文件: %s", conf_path)));
		}
		fprintf(conf_file, "pg_jieba.data_path_user_dict = '%s'\n", pg_jieba_data_path_user_dict);
		fclose(conf_file);
		elog(LOG, "pg_jieba: pg_jieba.data_path_user_dict save to %s", conf_path);
	}

	// 释放内存
	if (dict_path)
	{
		pfree(dict_path);
	}
    if (quoted_table_name && quoted_table_name != table_name) {
		pfree((void *)quoted_table_name);
	}
	if (table_name)
	{
		pfree(table_name);
	}

	local_data_path_user_dict = pstrdup(pg_jieba_data_path_user_dict);

	// 释放共享内存锁
	LWLockRelease(shared_state->lock);

	// 重新加载词典
	jieba_reload_dict_common();

    PG_RETURN_TEXT_P(cstring_to_text(local_data_path_user_dict));
}

Datum
jieba_dict_remove_table(PG_FUNCTION_ARGS)
{
	text *table_name_text;
    char *table_name;
	char conf_path[MAXPGPATH];
	char* dict_path;
	List *dict_name_list;
    ListCell *lc;
	FILE *conf_file;
	StringInfoData buf;
	char *local_data_path_user_dict = NULL;
	char *data_path_user_dict_copy;
	// 利用共享内存锁来防止并发操作
	LWLockAcquire(shared_state->lock, LW_EXCLUSIVE);
	// 从参数中接收表名
    table_name_text = PG_GETARG_TEXT_PP(0);
    table_name = text_to_cstring(table_name_text);

	// 从配置参数 pg_jieba.data_path_user_dict 中移除 table_name
	if (pg_jieba_data_path_user_dict && pg_jieba_data_path_user_dict[0] != '\0')
	{
		// 使用 ',' 作为分隔符
		data_path_user_dict_copy = pstrdup(pg_jieba_data_path_user_dict);
		if (!SplitIdentifierString(data_path_user_dict_copy, ',', &dict_name_list))
			ereport(ERROR, (errcode(ERRCODE_SYNTAX_ERROR), errmsg("pg_jieba: split dict_name_list failed")));

		// 判断列表中是否存在相同的table_name，并移除
		initStringInfo(&buf);
		foreach(lc, dict_name_list)
		{
			const char *dict_name = (const char *) lfirst(lc);
			if (strcmp(dict_name, table_name) != 0) // 只保留不等于table_name的项
			{
				if (buf.len > 0)
					appendStringInfoString(&buf, ",");
				appendStringInfoString(&buf, dict_name);
			}
		}
		edit_data_path_user_dict(buf.data);
		if (buf.data) {
			pfree(buf.data);
		}
		if (dict_name_list) {
			list_free(dict_name_list);
		}
		if (data_path_user_dict_copy) {
			pfree(data_path_user_dict_copy);
		}
	} else {
		edit_data_path_user_dict("");
	}

	// 覆盖 jieba.conf 中的配置
	snprintf(conf_path, MAXPGPATH, "%s/jieba.conf", DataDir);
	conf_file = fopen(conf_path, "w");
	if (conf_file == NULL)
	{
		ereport(ERROR, (errcode(ERRCODE_IO_ERROR), errmsg("无法打开文件: %s", conf_path)));
	}
	fprintf(conf_file, "pg_jieba.data_path_user_dict = '%s'\n", pg_jieba_data_path_user_dict);
	fclose(conf_file);
	elog(LOG, "pg_jieba: pg_jieba.data_path_user_dict remove table '%s'", table_name);

	// 移除字典文件
	dict_path = jieba_get_data_path_dict_filename(table_name, DICT_EXT);
	if (access(dict_path, F_OK) == 0) {
		unlink(dict_path);
	} else {
		elog(LOG, "pg_jieba: Dictionary file %s does not exist, don't need to remove.", dict_path);
	}
	if (dict_path) {
		pfree(dict_path);
	}

	local_data_path_user_dict = pstrdup(pg_jieba_data_path_user_dict);
	
	// 释放共享内存锁
	LWLockRelease(shared_state->lock);

	// 重新加载词典
	jieba_reload_dict_common();

	PG_RETURN_TEXT_P(cstring_to_text(local_data_path_user_dict));
}

static void
DefineCustomConfigVariables()
{
	DefineCustomStringVariable("pg_jieba.hmm_model",
							"hmm model file.",
							NULL,
							&pg_jieba_hmm_model,
							"jieba_hmm",
							PGC_POSTMASTER, 0,
							NULL,
							NULL,
							NULL);

	DefineCustomStringVariable("pg_jieba.base_dict",
							"base dictionary.",
							NULL,
							&pg_jieba_dict,
							"jieba_base",
							PGC_POSTMASTER, 0,
							NULL,
							NULL,
							NULL);

	DefineCustomStringVariable("pg_jieba.user_dict",
							"CSV list of specific user dictionary.",
							NULL,
							&pg_jieba_user_dict,
							"jieba_user",
							PGC_SIGHUP,
							GUC_LIST_INPUT,
							check_user_dict,
							assign_user_dict,
							NULL);

	DefineCustomStringVariable("pg_jieba.data_path_user_dict",
                            "user dictionary file in data path.",
                            NULL,
                            &pg_jieba_data_path_user_dict,
                            "",
                            PGC_SIGHUP,
                            GUC_LIST_INPUT,
                            check_data_path_user_dict,
                            assign_data_path_user_dict,
                            NULL);
}

static void
recompute_dicts_path(void)
{
	MemoryContext oldcxt;
	char	   *user_dicts;
	// char	   *new_dicts;

	JiebaCtx   *new_jieba = NULL;
	char* dict_path;
	char* hmm_model_path;

	/* Do nothing if path is already valid. */
	if (userDictsValid)
		return;

	dict_path = jieba_get_tsearch_config_filename(pg_jieba_dict, DICT_EXT);
	hmm_model_path = jieba_get_tsearch_config_filename(pg_jieba_hmm_model, MODEL_EXT);
	user_dicts = extract_dict_list(pg_jieba_user_dict);
	user_dicts = extract_data_path_dict_list(pg_jieba_data_path_user_dict, user_dicts);

	/*。
	 * Now that we've successfully built the new,
	 * save it in permanent storage.
	 */
	oldcxt = MemoryContextSwitchTo(TopMemoryContext);
	{
		// new_dicts = pstrdup(user_dicts);

		/*
		 init will take a few seconds to load dicts.
		 */
		new_jieba = Jieba_New(dict_path, hmm_model_path, user_dicts);
	}
	MemoryContextSwitchTo(oldcxt);

	/* Now safe to assign to state variables. */
	// if (userDicts)
	// 	pfree(userDicts);
	// userDicts = new_dicts;

	if (jieba) {
		Jieba_Free(jieba);
		jieba = NULL;
	}
	jieba = new_jieba;
	/* Mark the path valid. */
	userDictsValid = true;

	/* Clean up. */
	if (user_dicts) {
		pfree(user_dicts);
	}
	if (dict_path) {
		pfree(dict_path);
	}
	if (hmm_model_path) {
		pfree(hmm_model_path);
	}
}

/* check_hook: validate new value */
static bool
check_user_dict(char **newval, void **extra, GucSource source)
{
	char	   *rawname;
	List	   *namelist;

	/* Need a modifiable copy of string */
	rawname = pstrdup(*newval);

	/* Parse string into list of identifiers */
	if (!SplitIdentifierString(rawname, ',', &namelist))
	{
		/* syntax error in name list */
		GUC_check_errdetail("List syntax is invalid.");
		pfree(rawname);
		list_free(namelist);
		return false;
	}

	/*
	 * We used to try to check that the named schemas exist, but there are
	 * many valid use-cases for having search_path settings that include
	 * schemas that don't exist; and often, we are not inside a transaction
	 * here and so can't consult the system catalogs anyway.  So now, the only
	 * requirement is syntactic validity of the identifier list.
	 */

	pfree(rawname);
	list_free(namelist);

	return true;
}

/* assign_hook: do extra actions as needed */
static void
assign_user_dict(const char *newval, void *extra)
{
	/*
	 * We mark the path as needing recomputation, but don't do anything until
	 * it's needed.  This avoids trying to do database access during GUC
	 * initialization, or outside a transaction.
	 */
//	userDictsValid = false;
}

static bool
check_data_path_user_dict(char **newval, void **extra, GucSource source)
{
	char	   *rawname;
	List	   *namelist;

	rawname = pstrdup(*newval);

	if (!SplitIdentifierString(rawname, ',', &namelist))
	{
		/* syntax error in name list */
		GUC_check_errdetail("List syntax is invalid.");
		pfree(rawname);
		list_free(namelist);
		return false;
	}

	pfree(rawname);
	list_free(namelist);

	return true;
}

static void
assign_data_path_user_dict(const char *newval, void *extra)
{

}

/*
 * Given the base name and extension of a tsearch config file, return
 * its full path name.  The base name is assumed to be user-supplied,
 * and is checked to prevent pathname attacks.  The extension is assumed
 * to be safe.
 *
 * The result is a palloc'd string.
 */
static char*
jieba_get_tsearch_config_filename(const char *basename,
								  const char *extension)
{
	char		sharepath[MAXPGPATH];
	char	   *result;

	/*
	 * We limit the basename to contain a-z, 0-9, and underscores.  This may
	 * be overly restrictive, but we don't want to allow access to anything
	 * outside the tsearch_data directory, so for instance '/' *must* be
	 * rejected, and on some platforms '\' and ':' are risky as well. Allowing
	 * uppercase might result in incompatible behavior between case-sensitive
	 * and case-insensitive filesystems, and non-ASCII characters create other
	 * interesting risks, so on the whole a tight policy seems best.
	 */
	if (strspn(basename, "abcdefghijklmnopqrstuvwxyz0123456789_.") != strlen(basename))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("invalid text search configuration file name \"%s\"",
						basename)));

	get_share_path(my_exec_path, sharepath);
	result = palloc(MAXPGPATH);
	snprintf(result, MAXPGPATH, "%s/tsearch_data/%s.%s",
			 sharepath, basename, extension);

	return result;
}

/*
 * The result is a palloc'd string.
 */
static char *
extract_dict_list(const char *dictsString)
{
	List	   *elemlist;
	ListCell   *lc;
	char       *rawstring;

	bool		first;
	StringInfoData bufdata;
	StringInfo buf = &bufdata;

	initStringInfo(&bufdata);

	rawstring = pstrdup(dictsString);

	// Parse string into list of identifiers
	if (!SplitIdentifierString(rawstring, ',', &elemlist)) {
		// syntax error in list
		pfree(rawstring);
		list_free(elemlist);
		ereport(LOG,
				(errcode(ERRCODE_SYNTAX_ERROR),
				 errmsg("parameter must be a list of dictionary")));
		return NULL;
	}

	first = true;
	foreach(lc, elemlist)
	{
		const char *dict_name = (const char *) lfirst(lc);
		char* dict_path = jieba_get_tsearch_config_filename(dict_name, DICT_EXT);

		if (!first)
			appendStringInfoString(buf, ";");

		appendStringInfoString(buf, dict_path);

		pfree(dict_path);

		first = false;
	}

	list_free(elemlist);
	pfree(rawstring);

	return buf->data;
}

/*
 * 处理数据目录下字典的方法
 * The result is a palloc'd string.
 */
static char *
extract_data_path_dict_list(const char *dictsString, const char *userDictsString)
{
	List	   *elemlist;
	ListCell   *lc;
	char       *rawstring;
	char       *user_dicts_rawstring;

	bool		first;
	StringInfoData bufdata;
	StringInfo buf = &bufdata;

	initStringInfo(&bufdata);

	rawstring = pstrdup(dictsString);
	user_dicts_rawstring = userDictsString ? pstrdup(userDictsString) : NULL;

	// Parse string into list of identifiers
	if (!SplitIdentifierString(rawstring, ',', &elemlist)) {
		// syntax error in list
		pfree(rawstring);
		list_free(elemlist);
		ereport(LOG,
				(errcode(ERRCODE_SYNTAX_ERROR),
				 errmsg("parameter must be a list of dictionary")));
		return NULL;
	}

	first = true;
	if (user_dicts_rawstring && user_dicts_rawstring[0] != '\0') {
		appendStringInfoString(buf, user_dicts_rawstring);
		first = false;
	}
	foreach(lc, elemlist)
	{
		const char *dict_name = (const char *) lfirst(lc);
		char* dict_path = jieba_get_data_path_dict_filename(dict_name, DICT_EXT);

		// 检查文件是否存在
		if (access(dict_path, F_OK) == 0) {
			if (!first)
				appendStringInfoString(buf, ";");

			appendStringInfoString(buf, dict_path);
			first = false;
		} else {
			elog(LOG, "pg_jieba: Dictionary file %s does not exist, skipping.", dict_path);
		}

		if (dict_path) {
			pfree(dict_path);
		}
	}

	if (elemlist) {
		list_free(elemlist);
	}
	if (rawstring) {
		pfree(rawstring);
	}
	if (user_dicts_rawstring) {
		pfree(user_dicts_rawstring);
	}

	return buf->data;
}


/*
 * 拼接数据目录下的用户字典文件路径
 */
static char*
jieba_get_data_path_dict_filename(const char *basename, const char *extension)
{
    char *result;  // 添加变量声明

    if (strspn(basename, "abcdefghijklmnopqrstuvwxyz0123456789_.") != strlen(basename))
        ereport(ERROR,
                (errcode(ERRCODE_INVALID_PARAMETER_VALUE),
                 errmsg("invalid text search configuration file name \"%s\"",
                        basename)));
    
    /* 使用 DataDir 获取数据目录路径 */
    result = palloc(MAXPGPATH);
    snprintf(result, MAXPGPATH, "%s/%s.%s",
             DataDir, basename, extension);
             
    return result;
}



/*
 * 检测并刷新字典
 */
void check_and_refresh_dictionary(void)
{
    uint32 global_version;

    /* 获取全局版本号 */
    LWLockAcquire(shared_state->lock, LW_SHARED);
    global_version = shared_state->global_version;
    LWLockRelease(shared_state->lock);

    /* 如果版本号更新，刷新字典 */
    if (global_version != local_version)
    {
        elog(LOG, "pg_jieba: Dictionary refresh version from %u to %u, start...", local_version, global_version);
        userDictsValid = false;
   		recompute_dicts_path();
		elog(LOG, "pg_jieba: Dictionary refresh version from %u to %u finished ~", local_version, global_version);
        local_version = global_version;
    }
	else
	{
		elog(LOG, "pg_jieba: Dictionary don't need refresh --");
	}
}

/*
 * 计算SharedDictionaryState占用共享内存大小
 */
static Size
pg_jieba_shmem_size(void)
{
	Size size = 0;
	
	size = add_size(size, sizeof(SharedDictionaryState));
	return size;
}

/*
 * 添加共享内存请求函数
 */
static void
pg_jieba_shmem_request(void)
{
    /* 如果有之前的钩子，先调用 */
    if (prev_shmem_request_hook)
        prev_shmem_request_hook();
        
    /* 请求共享内存和LWLock */
    RequestAddinShmemSpace(pg_jieba_shmem_size());
    RequestNamedLWLockTranche("pg_jieba_shared_lock", 1);
}

/*
 * postmaster 的 SIGHUP 信号处理函数，pg_reload_conf()执行时会触发
 */
static void
pg_jieba_sighup_handler(SIGNAL_ARGS)
{
    /* 首先调用之前的处理函数（如果有的话） */
    if (prev_sighup_handler)
        prev_sighup_handler(postgres_signal_arg);

    elog(LOG, "pg_jieba: Postmaster received SIGHUP signal !!!");
    
    /* 检测并刷新字典 */
    if (shared_state != NULL)
    {
        check_and_refresh_dictionary();
    }
}

/*
 * backend process 的 SIGHUP 信号处理函数，pg_reload_conf()执行时会触发
 */
static void
pg_jieba_backend_sighup_handler(SIGNAL_ARGS)
{
    /* 首先调用之前的处理函数（如果有的话） */
    if (prev_sighup_handler_backend)
        prev_sighup_handler_backend(postgres_signal_arg);

    elog(LOG, "pg_jieba: Backend received SIGHUP signal !!!");
    
    /* 检测并刷新字典 */
    if (shared_state != NULL)
    {
        check_and_refresh_dictionary();
    }
}

/* 
 * 自定义的 ClientAuthentication 钩子函数
 * 登录成功才注册信号处理器
 */
static void
jieba_client_authentication(Port *port, int status)
{
    /* 登录成功才注册信号处理器 */
    if (status == STATUS_OK)
    {
        elog(LOG, "pg_jieba: Registering backend SIGHUP handler");
        prev_sighup_handler_backend = pqsignal(SIGHUP, pg_jieba_backend_sighup_handler);
    }

    /* 调用原始的 ClientAuthentication_hook（如果存在） */
    if (prev_ClientAuthentication)
        prev_ClientAuthentication(port, status);
}

/*
 * 更新字典版本号，并通知Postmaster刷新字典
 */
static void
jieba_reload_dict_common(void)
{
	/* 更新全局版本号前先获取锁 */
    if (!shared_state) {
        ereport(ERROR, (errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE), errmsg("pg_jieba: shared memory not initialized")));
    }
	/* 更新全局版本号 */
    LWLockAcquire(shared_state->lock, LW_EXCLUSIVE);
	if (shared_state->global_version == UINT32_MAX) {
        shared_state->global_version = 1;
    } else {
        shared_state->global_version++;
    }
    LWLockRelease(shared_state->lock);

	/* 发送 SIGHUP 信号给 Postmaster，用于通知刷新字典 */
    if (kill(PostmasterPid, SIGHUP))
    {
        ereport(WARNING, (errmsg("pg_jieba: failed to send SIGHUP signal to postmaster: %m")));
    } else {
        elog(LOG, "pg_jieba: SIGHUP signal sent to postmaster for reload dictionary");
    }
}

/*
 * 修改参数：pg_jieba.data_path_user_dict
 */
static void
edit_data_path_user_dict(const char *conf_val)
{
	set_config_option("pg_jieba.data_path_user_dict",
                     conf_val ? conf_val : "",  // 如果conf_val为NULL，使用空字符串
                     PGC_SIGHUP,
                     PGC_S_SESSION,
                     GUC_ACTION_SET,
                     true,  // is_local 本地是否也生效
                     0,     // elevel 错误等级
                     false  // is_reload 是否重新加载
                     );
}