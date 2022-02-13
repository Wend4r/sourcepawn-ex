/* vim: set ts=8 sts=2 sw=2 tw=99 et: */
#include "sctracker.h"

#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include <utility>

#include <amtl/am-raii.h>
// #include <amtl/am-vector.h>
#include <amtl/am-deque.h>
#include "emitter.h"
#include "lexer.h"
#include "sc.h"
#include "types.h"

struct MemoryUse
{
	MemoryUse(int type, int size)
	 : type(type),
	   size(size)
	{
		
	}

	int type; /* MEMUSE_STATIC or MEMUSE_DYNAMIC */
	int size; /* size of array for static (0 for dynamic) */
};

struct MemoryScope
{
	MemoryScope(MemoryScope&& other)
	 : scope_id(other.scope_id),
	   usage(std::move(other.usage))
	{}
	explicit MemoryScope(int scope_id)
	 : scope_id(scope_id)
	{

	}

	MemoryScope(const MemoryScope& other) = delete;

	MemoryScope& operator =(const MemoryScope& other) = delete;
	MemoryScope& operator =(MemoryScope&& other)
	{
		scope_id = other.scope_id;
		usage = std::move(other.usage);
		return *this;
	}

	int scope_id;
	std::vector<MemoryUse> usage;
};

std::deque<MemoryScope> sStackScopes;
std::deque<MemoryScope> sHeapScopes;
std::deque<std::unique_ptr<funcenum_t>> sFuncEnums;
std::deque<std::unique_ptr<pstruct_t>> sStructs;
std::deque<std::unique_ptr<methodmap_t>> sMethodmaps;

pstruct_t::pstruct_t(const char* name)
{
	ke::SafeStrcpy(this->name, sizeof(this->name), name);
}

const structarg_t*
pstructs_getarg(const pstruct_t* pstruct, sp::Atom* name)
{
	for(const auto& arg : pstruct->args)
	{
		if(arg->name == name)
		{
			return arg.get();
		}
	}

	return nullptr;
}

pstruct_t*
pstructs_add(const char* name)
{
	auto p = std::make_unique<pstruct_t>(name);

	sStructs.push_back(std::move(p));

	return sStructs.back().get();
}

void
pstructs_free()
{
	sStructs.clear();
}

pstruct_t*
pstructs_find(const char* name)
{
	for(const auto& p : sStructs)
	{
		if(!strcmp(p->name, name))
		{
			return p.get();
		}
	}

	return nullptr;
}

structarg_t*
pstructs_addarg(pstruct_t* pstruct, const structarg_t* arg)
{
	structarg_t *pResult = nullptr;

	if(!pstructs_getarg(pstruct, arg->name))
	{
		auto newarg = std::make_unique<structarg_t>();

		memcpy(newarg.get(), arg, sizeof(structarg_t));
	
		newarg->offs = static_cast<unsigned int>(pstruct->args.size()) * sizeof(cell);
		newarg->index = static_cast<unsigned int>(pstruct->args.size());

		pstruct->args.push_back(std::move(newarg));

		pResult = pstruct->args.back().get();
	}

	return pResult;
}

void
funcenums_free()
{
	sFuncEnums.clear();
}

funcenum_t*
funcenums_add_or_find(const char* name)
{
	auto e = std::make_unique<funcenum_t>();

	strcpy(e->name, name);
	e->display_name[0] = '\0';

	e->tag = gTypes.defineFunction(name, e.get())->tagid();

	sFuncEnums.push_back(std::move(e));

	return sFuncEnums.back().get();
}

funcenum_t*
funcenums_add_or_find(const char* name, const char* display_name)
{
	funcenum_t *pE = funcenums_add_or_find(name);

	strcpy(pE->display_name, display_name);

	return pE;
}

funcenum_t*
funcenum_for_symbol(symbol* sym)
{
	functag_t* ft = new functag_t;

	ft->ret_tag = sym->tag;

	for(arginfo& arg : sym->function()->args)
	{
		if(arg.ident)
		{
			funcarg_t dest;

			dest.tag = arg.tag;
			dest.dimcount = arg.numdim;

			memcpy(dest.dims, arg.dim, arg.numdim * sizeof(int));
			memcpy(dest.idxtag, arg.idxtag, arg.numdim * sizeof(int));

			dest.ident = arg.ident;
			dest.fconst = arg.is_const;

			ft->args.push_back(dest);
		}
	}

	char sName[METHOD_NAMEMAX + 1];

	ke::SafeSprintf(sName, sizeof(sName), "::ft:%s:%d:%d", sym->name(), sym->addr(), sym->codeaddr);

	funcenum_t *pFuncEnum = funcenums_add_or_find(sName, sym->name());

	functags_add_or_find(pFuncEnum, ft);

	return pFuncEnum;
}

// Finds a functag that was created intrinsically.
functag_t*
functag_find_intrinsic(int tag)
{
	funcenum_t* pFuncEnum = gTypes.find(tag)->asFunction();

	return pFuncEnum && !strncmp(pFuncEnum->name, "::ft:", 5) && !pFuncEnum->entries.empty() ? pFuncEnum->entries.back() : nullptr;
}

void
functags_add_or_find(funcenum_t* en, functag_t* src)
{
	en->entries.push_back(src);
}

static void
EnterMemoryScope(std::deque<MemoryScope> &frame)
{
	frame.push_back(frame.empty() ? MemoryScope{0} : MemoryScope{frame.back().scope_id + 1});
}

static void
AllocInScope(MemoryScope& scope, int type, int size)
{
	if(type == MEMUSE_STATIC && !scope.usage.empty() && scope.usage.back().type == MEMUSE_STATIC)
	{
		scope.usage.back().size += size;
	}
	else
	{
		scope.usage.push_back(MemoryUse{type, size});
	}
}

void
pushheaplist()
{
	EnterMemoryScope(sHeapScopes);
}

// Sums up array usage in the current heap tracer and convert it into a dynamic array.
// This is used for the ternary operator, which needs to convert its array usage into
// something dynamically managed.
// !Note:
// This might break if expressions can ever return dynamic arrays.
// Thus, we assert() if something is non-static here.
// Right now, this poses no problem because this type of expression is impossible:
//   (a() ? return_array() : return_array()) ? return_array() : return_array()
cell_t
pop_static_heaplist()
{
	cell_t total = 0;

	for(const auto& use : sHeapScopes.back().usage)
	{
		assert(use.type == MEMUSE_STATIC);
		total += use.size;
	}

	sHeapScopes.pop_back();

	return total;
}

int
markheap(int type, int size)
{
	AllocInScope(sHeapScopes.back(), type, size);

	return size;
}

void
pushstacklist()
{
	EnterMemoryScope(sStackScopes);
}

int
markstack(int type, int size)
{
	AllocInScope(sStackScopes.back(), type, size);

	return size;
}

// Generates code to free all heap allocations on a tracker
static void
modheap_for_scope(const MemoryScope& scope)
{
	for(size_t i = scope.usage.size() - 1; i < scope.usage.size(); i--)
	{
		const MemoryUse& use = scope.usage[i];

		if(use.type == MEMUSE_STATIC)
		{
			modheap((-1) * use.size * sizeof(cell));
		}
		else
		{
			modheap_i();
		}
	}
}

void
modstk_for_scope(const MemoryScope &Scope)
{
	cell_t total = 0;

	for(const auto& use : Scope.usage)
	{
		assert(use.type == MEMUSE_STATIC);
		total += use.size;
	}

	modstk(total * sizeof(cell));
}

void
popheaplist(bool codegen)
{
	if(codegen)
	{
		modheap_for_scope(sHeapScopes.back());
	}

	sHeapScopes.pop_back();
}

void
genstackfree(int iStopID)
{
	for(size_t i = sStackScopes.size() - 1; i < sStackScopes.size(); i--)
	{
		const MemoryScope &Scope = sStackScopes[i];

		if(Scope.scope_id > iStopID)
		{
			modstk_for_scope(Scope);
		}
		else
		{
			break;
		}
	}
}

void
genheapfree(int stop_id)
{
	for(size_t i = sHeapScopes.size() - 1; i < sHeapScopes.size(); i--)
	{
		const MemoryScope& scope = sHeapScopes[i];

		if(scope.scope_id > stop_id)
		{
			modheap_for_scope(scope);
		}
		else
		{
			break;
		}
	}
}

void
popstacklist(bool codegen)
{
	if(codegen)
	{
		modstk_for_scope(sStackScopes.back());
	}

	sStackScopes.pop_back();
}

void
resetstacklist()
{
	sStackScopes.clear();
}

void
resetheaplist()
{
	sHeapScopes.clear();
}

int
stack_scope_id()
{
	return sStackScopes.back().scope_id;
}

methodmap_t::methodmap_t(methodmap_t *parent, LayoutSpec spec, const char *name)
	:parent(parent), tag(0), nullable(false), keyword_nullable(false), spec(spec), dtor(nullptr), ctor(nullptr)
{
	ke::SafeStrcpy(this->name, sizeof(this->name), name);
}

methodmap_t*
methodmap_add(methodmap_t* parent, LayoutSpec spec, const char* name)
{
	auto map = std::make_unique<methodmap_t>(parent, spec, name);

	if(spec == Layout_MethodMap && parent)
	{
		if(parent->nullable)
		{
			map->nullable = parent->nullable;
		}

		if(parent->keyword_nullable)
		{
			map->keyword_nullable = parent->keyword_nullable;
		}
	}

	if(spec == Layout_MethodMap)
	{
		map->tag = gTypes.defineMethodmap(name, map.get())->tagid();
	}
	else
	{
		map->tag = gTypes.defineObject(name)->tagid();
	}

	sMethodmaps.push_back(std::move(map));

	return sMethodmaps.back().get();
}

methodmap_t*
methodmap_find_by_tag(int tag)
{
	return gTypes.find(tag)->asMethodmap();
}

methodmap_t*
methodmap_find_by_name(const char* name)
{
	int tag = pc_findtag(name);

	return tag != -1 ? methodmap_find_by_tag(tag) : NULL;
}

methodmap_method_t*
methodmap_find_method(methodmap_t* map, const char* name)
{
	for(const auto& method : map->methods)
	{
		if(!strcmp(method->name, name))
		{
			return method.get();
		}
	}

	return map->parent ? methodmap_find_method(map->parent, name) : nullptr;
}

void
methodmaps_free()
{
	sMethodmaps.clear();
}

LayoutSpec
deduce_layout_spec_by_tag(int tag)
{
	if(methodmap_t* map = methodmap_find_by_tag(tag))
	{
		return map->spec;
	}

	Type* type = gTypes.find(tag);

	if(type && type->isFunction())
	{
		return Layout_FuncTag;
	}

	if(type && type->isStruct())
	{
		return Layout_PawnStruct;
	}

	if(Type* type = gTypes.find(tag))
	{
		if(findglb(type->name()))
		{
			return Layout_Enum;
		}
	}

	return Layout_None;
}

LayoutSpec
deduce_layout_spec_by_name(const char* name)
{
	Type* type = gTypes.find(name);
	if(!type)
		return Layout_None;

	return deduce_layout_spec_by_tag(type->tagid());
}

const char*
layout_spec_name(LayoutSpec spec)
{
	switch(spec) {
		case Layout_None:
			return "<none>";
		case Layout_Enum:
			return "enum";
		case Layout_FuncTag:
			return "functag";
		case Layout_PawnStruct:
			return "deprecated-struct";
		case Layout_MethodMap:
			return "methodmap";
		case Layout_Class:
			return "class";
	}
	return "<unknown>";
}

bool
can_redef_layout_spec(LayoutSpec def1, LayoutSpec def2)
{
	// Normalize the ordering, since these checks are symmetrical.
	if(def1 > def2) {
		LayoutSpec temp = def2;
		def2 = def1;
		def1 = temp;
	}

	switch(def1) {
		case Layout_None:
			return true;
		case Layout_Enum:
			if(def2 == Layout_Enum || def2 == Layout_FuncTag)
				return true;
			return def2 == Layout_MethodMap;
		case Layout_FuncTag:
			return def2 == Layout_Enum || def2 == Layout_FuncTag;
		case Layout_PawnStruct:
		case Layout_MethodMap:
			return false;
		case Layout_Class:
			return false;
	}
	return false;
}
