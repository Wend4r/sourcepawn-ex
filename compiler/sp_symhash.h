/* vim: set ts=4 sw=4 tw=99 et: */
#ifndef _INCLUDE_SPCOMP_SYMHASH_H_
#define _INCLUDE_SPCOMP_SYMHASH_H_

#include <amtl/am-hashtable.h>
#include <stddef.h>
#include <string.h>
#include "sc.h"
#include "shared/string-pool.h"

struct KeywordTablePolicy
{
	static bool matches(const sp::CharsAndLength& a, const sp::CharsAndLength& b)
	{
		return a.length() == b.length() && !strncmp(a.str(), b.str(), a.length());
	}
	static uint32_t hash(const sp::CharsAndLength& key)
	{
		return ke::HashCharSequence(key.str(), key.length());
	}
};

uint32_t NameHash(const char* str);

struct HashTable;

HashTable* NewHashTable();
void DestroyHashTable(HashTable* ht);
void AddToHashTable(HashTable* ht, symbol* sym);
void RemoveFromHashTable(HashTable* ht, symbol* sym);
symbol* FindInHashTable(HashTable* ht, const char* name, int fnumber);

#endif /* _INCLUDE_SPCOMP_SYMHASH_H_ */
