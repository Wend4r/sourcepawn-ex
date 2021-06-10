// vim: set ts=8 sts=4 sw=4 tw=99 et:
//  Pawn compiler - Recursive descend expresion parser
//
//  Copyright (c) ITB CompuPhase, 1997-2005
//
//  This software is provided "as-is", without any express or implied warranty.
//  In no event will the authors be held liable for any damages arising from
//  the use of this software.
//
//  Permission is granted to anyone to use this software for any purpose,
//  including commercial applications, and to alter it and redistribute it
//  freely, subject to the following restrictions:
//
//  1.  The origin of this software must not be misrepresented; you must not
//      claim that you wrote the original software. If you use this software in
//      a product, an acknowledgment in the product documentation would be
//      appreciated but is not required.
//  2.  Altered source versions must be plainly marked as such, and must not be
//      misrepresented as being the original software.
//  3.  This notice may not be removed or altered from any source distribution.
//
//  Version: $Id$

#include <assert.h>
#include <string.h>

#include <amtl/am-raii.h>
#include "emitter.h"
#include "errors.h"
#include "lexer.h"
#include "new-parser.h"
#include "optimizer.h"
#include "parse-node.h"
#include "sc.h"
#include "sclist.h"
#include "sctracker.h"
#include "scvars.h"
#include "types.h"

using namespace sp;

void
Parser::parse()
{
	while(freading)
	{
		Stmt *pDeclInfo = nullptr;

		token_t iToken;

		switch(lextok(&iToken))
		{
			case 0:
			{
				/* ignore zero's */
				break;
			}

			case tSYMBOL:
			{
				// Fallthrough.
			}

			case tINT:
			case tOBJECT:
			case tCHAR:
			case tVOID:
			case tLABEL:
			{
				lexpush();
				// Fallthrough.
			}

			case tNEW:
			case tDECL:
			case tSTATIC:
			case tPUBLIC:
			case tSTOCK:
			case tOPERATOR:
			case tNATIVE:
			case tFORWARD:
			{
				pDeclInfo = parse_unknown_decl(&iToken);

				break;
			}

			case tFUNCENUM:
			case tFUNCTAG:
			{
				error(FATAL_ERROR_FUNCENUM);

				break;
			}

			case tTYPEDEF:
			{
				pDeclInfo = parse_typedef();

				break;
			}

			case tTYPESET:
			{
				pDeclInfo = parse_typeset();

				break;
			}

			case tSTRUCT:
			{
				pDeclInfo = parse_pstruct();

				break;
			}

			case tCONST:
			{
				// pDeclInfo = parse_unknown_decl(&iToken);
				pDeclInfo = parse_const(sGLOBAL);

				break;
			}

			case tENUM:
			{
				if(matchtoken(tSTRUCT))
				{
					decl_enumstruct();
				}
				else
				{
					decl_enum(sGLOBAL);
					// decl = parse_enum(sGLOBAL);
				}

				break;
			}

			case tMETHODMAP:
			{
				domethodmap(Layout_MethodMap);

				break;
			}

			case tUSING:
			{
				pDeclInfo = parse_using();

				break;
			}

			case '}':
			{
				error_once(54); /* unmatched closing brace */

				break;
			}

			case '{':
			{
				error_once(55); /* start of function body without function header */

				break;
			}

			default:
			{
				if(freading)
				{
					error_once(10);    /* illegal function or declaration */
					lexclr(TRUE); /* drop the rest of the line */

					litidx = 0;   /* drop any literal arrays (strings) */
				}
			}
		}

		// Until we can eliminate the two-pass parser, top-level decls must be
		// resolved immediately.
		if(pDeclInfo)
		{
			pDeclInfo->Process();
		}
	}
}

Stmt*
Parser::parse_unknown_decl(const token_t *pToken)
{
	declinfo_t DeclInfo;

	if(pToken->id == tNATIVE || pToken->id == tFORWARD)
	{
		parse_decl(&DeclInfo, DECLFLAG_MAYBE_FUNCTION);
		funcstub(pToken->id, &DeclInfo, NULL);

		return nullptr;
	}

	auto pos = current_pos();

	int fpublic = FALSE, fstock = FALSE, fstatic = FALSE;

	switch(pToken->id)
	{
		case tPUBLIC:
		{
			fpublic = TRUE;

			break;
		}

		case tSTOCK:
		{
			fstock = TRUE;

			if(matchtoken(tSTATIC))
			{
				fstatic = TRUE;
			}

			break;
		}

		case tSTATIC:
		{
			fstatic = TRUE;

			// For compatibility, we must include this case. Though "stock" should
			// come first.
			if(matchtoken(tSTOCK))
			{
				fstock = TRUE;
			}

			break;
		}
	}

	int iFlags = DECLFLAG_MAYBE_FUNCTION | DECLFLAG_VARIABLE | DECLFLAG_ENUMROOT;

	if(pToken->id == tNEW)
	{
		iFlags |= DECLFLAG_OLD;
	}

	if(!parse_decl(&DeclInfo, iFlags))
	{
		// Error will have been reported earlier. Reset |decl| so we don't crash
		// thinking tag -1 has every flag.
		DeclInfo.type.tag = 0;
	}

	// Hacky bag o' hints as to whether this is a variable decl.
	bool probablyVariable = pToken->id == tNEW || DeclInfo.type.has_postdims || !lexpeek('(') || DeclInfo.type.is_const;

	if(!DeclInfo.opertok && probablyVariable)
	{
		if(pToken->id == tNEW && DeclInfo.type.is_new)
		{
			error_once(143);
		}

		Type *pType = gTypes.find(DeclInfo.type.tag);

		if(pType && pType->kind() == TypeKind::Struct)
		{
			Expr *pInit = nullptr;

			if(matchtoken('='))
			{
				needtoken('{');
				pInit = struct_init();
			}

			matchtoken(';');

			// Without an initializer, the stock keyword is implied.

			return new VarDecl(pos, gAtoms.add(DeclInfo.name), DeclInfo.type, sGLOBAL, fpublic && pInit, false, !pInit, pInit);
		}

		declglb(&DeclInfo, fpublic, fstatic, fstock);
	}
	else
	{
		if(!newfunc(&DeclInfo, NULL, fpublic, fstatic, fstock, NULL))
		{
			// Illegal function or declaration. Drop the line, reset literal queue.
			error_once(10);
			lexclr(TRUE);

			litidx = 0;
		}
	}

	return nullptr;
}

// Not stable.
Decl*
Parser::parse_enum(int vclass)
{
	token_pos_t pos = current_pos();

	cell val;

	char *sName;

	Atom *pLabel = nullptr;

	int iLex = lex(&val, &sName);

	if(iLex == tLABEL)
	{
		pLabel = gAtoms.add(sName);

		if(pLabel)
		{
			strcpy(sName, pLabel->chars());
		}
	}
	else
	{
		lexpush();
	}

	Atom *pName = nullptr;

	if(lex(&val, &sName) == tSYMBOL)
	{
		pName = gAtoms.add(sName);
	}
	else
	{
		lexpush();
	}

	EnumDecl *decl = new EnumDecl(pos, vclass, pLabel, pName);

	symbol *root;

	if(findglb(sName) || findconst(sName))
	{
		error(21, sName);
	}
	else
	{
		root = add_constant(sName, 0, sGLOBAL, 0);
		root->usage |= uREAD;
		root->enumroot = true;
		root->tag = gTypes.defineEnumTag(sName)->tagid();
	}

	needtoken('{');

	cell iIncrement = 1, 
	     iMultiplier = 1;

	if(matchtoken('('))
	{
		if(matchtoken(taADD))
		{
			exprconst(&iIncrement, NULL, NULL);
		}
		else if(matchtoken(taMULT))
		{
			exprconst(&iMultiplier, NULL, NULL);
		}
		else if(matchtoken(taSHL))
		{
			exprconst(&val, NULL, NULL);

			while(val-- > 0)
			{
				iMultiplier *= 2;
			}
		}
		needtoken(')');
	}

	cell iSize,
	     iPosition = 0,
	     iValue = 0;

	do
	{
		if(matchtoken('}'))
		{
			lexpush();
			break;
		}

		if(matchtoken(tLABEL))
		{
			error_once(153);
		}

		sp::Atom* pFieldName = nullptr;

		if(needtoken(tSYMBOL))
		{
			tokeninfo(&val, &sName);
			pFieldName = gAtoms.add(sName);
		}

		auto pos = current_pos();

		iSize = iIncrement;

		if(matchtoken('['))
		{
			error_once(153);
			exprconst(&iSize, nullptr, nullptr);
			needtoken(']');
		}
		if(matchtoken('='))
		{
			exprconst(&iValue, nullptr, nullptr);
		}

		if(pFieldName)
		{
			decl->fields().push_back(EnumField(pos, pFieldName, iValue));
		}

		if(iMultiplier == 1)
		{
			iValue += iSize;
		}
		else
		{
			iValue *= iSize * iMultiplier;
		}

		iPosition++;
	}
	while(matchtoken(','));

	needtoken('}');
	matchtoken(';');

	return decl;
}

Decl*
Parser::parse_pstruct()
{
	PstructDecl* struct_decl = nullptr;

	auto pos = current_pos();

	token_ident_t ident = {};

	if(needsymbol(&ident))
	{
		struct_decl = new PstructDecl(pos, gAtoms.add(ident.name));
	}

	needtoken('{');

	do
	{
		if(matchtoken('}'))
		{
			/* Quick exit */
			lexpush();

			break;
		}

		declinfo_t DeclInfo = {};

		DeclInfo.type.ident = iVARIABLE;
		DeclInfo.type.size = 1;

		needtoken(tPUBLIC);

		auto pos = current_pos();

		if(!parse_new_decl(&DeclInfo, nullptr, DECLFLAG_FIELD))
		{
			lexclr(TRUE);

			continue;
		}

		if(struct_decl)
		{
			struct_decl->fields().push_back(StructField(pos, gAtoms.add(DeclInfo.name), DeclInfo.type));
		}

		require_newline(TerminatorPolicy::NewlineOrSemicolon);
	}
	while(!lexpeek('}'));

	needtoken('}');
	matchtoken(';'); // eat up optional semicolon

	return struct_decl;
}

Decl*
Parser::parse_typedef()
{
	auto pos = current_pos();

	token_ident_t ident;

	if(!needsymbol(&ident))
	{
		return new ErrorDecl();
	}

	needtoken('=');

	return new TypedefDecl(pos, gAtoms.add(ident.name), parse_function_type());
}

Decl*
Parser::parse_typeset()
{
	auto pos = current_pos();

	token_ident_t ident;

	if(!needsymbol(&ident))
	{
		return new ErrorDecl();
	}

	TypesetDecl* decl = new TypesetDecl(pos, gAtoms.add(ident.name));

	needtoken('{');

	while(!matchtoken('}'))
	{
		auto type = parse_function_type();
		decl->types().push_back(type);
	}

	require_newline(TerminatorPolicy::NewlineOrSemicolon);

	return decl;
}

Decl*
Parser::parse_using()
{
	auto pos = current_pos();

	token_ident_t ident;

	if(!(needsymbol(&ident) && !strcmp(ident.name, "__intrinsics__") && needtoken('.') && needsymbol(&ident)))
	{
		error_once(156);
		lexclr(TRUE);

		return new ErrorDecl();
	}

	require_newline(TerminatorPolicy::Semicolon);

	return new UsingDecl(pos, gAtoms.add(ident.name));
}

Stmt*
Parser::parse_const(int vclass)
{
	StmtList* list = nullptr;
	Stmt* decl = nullptr;

	do
	{
		auto pos = current_pos();

		// Since spcomp is terrible, it's hard to use parse_decl() here - there
		// are all sorts of restrictions on const. We just implement some quick
		// detection instead.
		int tag = 0;
		token_t iToken;

		switch(lextok(&iToken))
		{
			case tINT:
			case tOBJECT:
			case tCHAR:
			{
				tag = parse_new_typename(&iToken);

				break;
			}

			case tLABEL:
			{
				tag = pc_addtag(iToken.str);

				break;
			}

			case tSYMBOL:
			{
				// See if we can peek ahead another symbol.
				if(lexpeek(tSYMBOL))
				{
					// This is a new-style declaration.
					tag = parse_new_typename(&iToken);
				}
				else
				{
					// Otherwise, we got "const X ..." so the tag is int. Give the
					// symbol back to the lexer so we get it as the name.
					lexpush();
				}

				break;
			}

			default:
			{
				error_once(122);

				break;
			}
		}

		sp::Atom* name = nullptr;

		if(expecttoken(tSYMBOL, &iToken))
		{
			name = gAtoms.add(iToken.str);
		}

		// auto Stmts = list->stmts();

		// for(auto Stmt : Stmts)
		// {
			
		// }

		// Stmts.push_back(decl);

		needtoken('=');

		int expr_val, expr_tag;

		exprconst(&expr_val, &expr_tag, nullptr);

		typeinfo_t type = {};

		type.size = 1;
		type.tag = tag;
		type.is_const = true;

		if(name)
		{
			VarDecl* var = new ConstDecl(pos, name, type, vclass, expr_tag, expr_val);

			if(decl)
			{
				if(!list)
				{
					list = new StmtList(var->pos());

					list->stmts().push_back(decl);
				}

				list->stmts().push_back(var);
			}
			else
			{
				decl = var;
			}
		}
	}
	while(matchtoken(','));

	needtoken(tTERM);

	return list ? list : decl;
}

int
Parser::expression(value* lval)
{
	Expr* expr = hier14();

	if(!expr->Bind() || !expr->Analyze())
	{
		sideeffect = TRUE;
		*lval = value::ErrorValue();

		return FALSE;
	}

	expr->ProcessUses();

	*lval = expr->val();

	if(cc_ok())
	{
		expr->Emit();
	}

	sideeffect = expr->HasSideEffects();

	return expr->lvalue();
}

Expr*
Parser::hier14()
{
	Expr* node = hier13();

	int iToken = lex();

	auto pos = current_pos();

	switch(iToken)
	{
		case taOR:
		case taXOR:
		case taAND:
		case taADD:
		case taSUB:
		case taMULT:
		case taDIV:
		case taMOD:
		case taSHRU:
		case taSHR:
		case taSHL:
		{
			break;
		}
		case '=': /* simple assignment */
		{
			if(sc_intest)
			{
				error_once(211); /* possibly unintended assignment */
			}

			break;
		}
		default:
		{
			lexpush();

			return node;
		}
	}

	Expr *pRight = hier14();

	return new BinaryExpr(pos, iToken, node, pRight);
}

Expr*
Parser::plnge(int* piOperatorList, NewHierFn hier)
{
	int iOperatorIndex;

	Expr* pNode = (this->*hier)();

	if(!nextop(&iOperatorIndex, piOperatorList))
	{
		return pNode;
	}

	do
	{
		const token_pos_t &Position = current_pos();

		Expr* pRight = (this->*hier)();

		int iToken = piOperatorList[iOperatorIndex];

		switch(iToken)
		{
			case tlOR:
			case tlAND:
			{
				pNode = new LogicalExpr(Position, iToken, pNode, pRight);
				break;
			}

			default:
			{
				pNode = new BinaryExpr(Position, iToken, pNode, pRight);
				break;
			}
		}
	}
	while(nextop(&iOperatorIndex, piOperatorList));

	return pNode;
}

Expr*
Parser::plnge_rel(int* piOperatorList, NewHierFn hier)
{
	int iOperatorIndex;

	Expr* pFirst = (this->*hier)();

	if(!nextop(&iOperatorIndex, piOperatorList))
	{
		return pFirst;
	}

	ChainedCompareExpr* pChain = new ChainedCompareExpr(current_pos(), pFirst);

	do
	{
		const token_pos_t &Position = current_pos();

		Expr* pRight = (this->*hier)();

		// printf("opstr[iOperatorIndex] = %i ([-1] = %i)\n", piOperatorList[iOperatorIndex], piOperatorList[iOperatorIndex - 1]);

		pChain->ops().push_back(CompareOp(Position, piOperatorList[iOperatorIndex], pRight));
	}
	while(nextop(&iOperatorIndex, piOperatorList));

	return pChain;
}

Expr*
Parser::hier13()
{
	Expr* pNode = hier12();

	if(matchtoken('?'))
	{
		auto pos = current_pos();

		Expr* pLeft;

		{
			/* do not allow tagnames here (colon is a special token) */
			ke::SaveAndSet<bool> allowtags(&sc_allowtags, false);
			pLeft = hier13();
		}

		needtoken(':');

		return new TernaryExpr(pos, pNode, pLeft, hier13());
	}

	return pNode;
}

Expr*
Parser::hier12()
{
	return plnge(list12, &Parser::hier11);
}

Expr*
Parser::hier11()
{
	return plnge(list11, &Parser::hier10);
}

Expr*
Parser::hier10()
{
	return plnge(list10, &Parser::hier9);
}

Expr*
Parser::hier9()
{
	return plnge_rel(list9, &Parser::hier8);
}

Expr*
Parser::hier8()
{
	return plnge(list8, &Parser::hier7);
}

Expr*
Parser::hier7()
{
	return plnge(list7, &Parser::hier6);
}

Expr*
Parser::hier6()
{
	return plnge(list6, &Parser::hier5);
}

Expr*
Parser::hier5()
{
	return plnge(list5, &Parser::hier4);
}

Expr*
Parser::hier4()
{
	return plnge(list4, &Parser::hier3);
}

Expr*
Parser::hier3()
{
	return plnge(list3, &Parser::hier2);
}

Expr*
Parser::hier2()
{
	int iTokenValue;

	char* sTokenStr;

	int iTok = lex(&iTokenValue, &sTokenStr);

	const token_pos_t &Position = current_pos();

	switch(iTok)
	{
		case tINC: /* ++lval */
		case tDEC: /* --lval */
		{
			Expr *pNode = hier2();

			return new PreIncExpr(Position, iTok, pNode);
		}

		case '~':
		case '-':
		case '!':
		{
			Expr* pNode = hier2();

			return new UnaryExpr(Position, iTok, pNode);
		}

		case tNEW:
		{
			token_ident_t ident;

			if(!needsymbol(&ident))
			{
				return new ErrorExpr();
			}

			Expr *pTarget = new SymbolExpr(current_pos(), gAtoms.add(ident.name));

			needtoken('(');

			return parse_call(Position, iTok, pTarget);
		}

		case tLABEL: /* tagname override */
		{
			int iTag = pc_addtag(sTokenStr);

			if(sc_require_newdecls)
			{
				// Warn: old style cast used when newdecls pragma is enabled
				error(240, sTokenStr, type_to_name(iTag));
			}

			Expr* pExpr = hier2();

			return new CastExpr(Position, iTok, iTag, pExpr);
		}

		case tDEFINED:
		{
			int iParents = 0;

			while(matchtoken('('))
			{
				iParents++;
			}

			token_ident_t ident;

			if(!needsymbol(&ident))
			{
				return new ErrorExpr();
			}

			while(iParents--)
			{
				needtoken(')');
			}

			return new IsDefinedExpr(Position, gAtoms.add(ident.name));
		}

		case tSIZEOF:
		{
			int iParents = 0;

			while(matchtoken('('))
			{
				iParents++;
			}

			token_ident_t ident;

			if(!needsymbol(&ident))
			{
				return new ErrorExpr();
			}

			int iArrayLevels = 0;

			while(matchtoken('['))
			{
				iArrayLevels++;

				needtoken(']');
			}

			Atom* pField = nullptr;

			int iToken = lex(&iTokenValue, &sTokenStr);

			if(iToken == tDBLCOLON || iToken == '.')
			{
				token_ident_t field_name;

				if(!needsymbol(&field_name))
				{
					return new ErrorExpr();
				}

				pField = gAtoms.add(field_name.name);
			}
			else
			{
				lexpush();

				iToken = 0;
			}

			while(iParents--)
			{
				needtoken(')');
			}

			Atom* pName = gAtoms.add(ident.name);

			return new SizeofExpr(Position, pName, pField, iToken, iArrayLevels);
		}

		default:
		{
			lexpush();

			break;
		}
	}

	Expr* pNode = hier1();

	/* check for postfix operators */
	if(matchtoken(';'))
	{
		/* Found a ';', do not look further for postfix operators */
		lexpush(); /* push ';' back after successful match */

		return pNode;
	}

	if(matchtoken(tTERM))
	{
		/**
		 * Found a newline that ends a statement (this is the case when
		 * semicolons are optional). Note that an explicit semicolon was
		 * handled above. This case is similar, except that the token must
		 * not be pushed back.
		 */
		return pNode;
	}

	switch(iTok = lex(&iTokenValue, &sTokenStr))
	{
		case tINC: /* lval++ */
		case tDEC: /* lval-- */
		{
			return new PostIncExpr(current_pos(), iTok, pNode);
		}

		default:
		{
			lexpush();
			break;
		}
	}

	return pNode;
}

Expr*
Parser::hier1()
{
	Expr *base = matchtoken(tVIEW_AS) ? parse_view_as() : primary();

	for(;;)
	{
		char* st;
		cell val;

		int iToken = lex(&val, &st);

		if(iToken == '.' || iToken == tDBLCOLON)
		{
			auto pos = current_pos();

			token_ident_t ident;

			if(!needsymbol(&ident))
			{
				break;
			}

			if(false)
			{
				// Enum struct fields array index.
				Expr* inner = hier14();

				base = new IndexExpr(pos, base, inner);
			}
			else
			{
				base = new FieldAccessExpr(pos, iToken, base, gAtoms.add(ident.name));
			}
		}
		else if(iToken == '[')
		{
			auto pos = current_pos();

			Expr* inner = hier14();

			base = new IndexExpr(pos, base, inner);

			needtoken(']');
		}
		else if(iToken == '(')
		{
			auto pos = current_pos();

			base = parse_call(pos, iToken, base);
		}
		else
		{
			lexpush();

			break;
		}
	}

	return base;
}

Expr*
Parser::primary()
{
	if(matchtoken('(')) { /* sub-expression - (expression,...) */
		/* no longer in "test" expression */
		ke::SaveAndSet<bool> in_test(&sc_intest, false);
		/* allow tagnames to be used in parenthesized expressions */
		ke::SaveAndSet<bool> allowtags(&sc_allowtags, true);

		CommaExpr* expr = new CommaExpr(current_pos());
		do {
			Expr* child = hier14();
			expr->exprs().push_back(child);
		} while(matchtoken(','));
		needtoken(')');
		lexclr(FALSE); /* clear lex() push-back, it should have been
						* cleared already by needtoken() */
		return expr;
	}

	cell val;
	char* st;
	int iToken = lex(&val, &st);

	if(iToken == tTHIS)
		return new ThisExpr(current_pos());
	if(iToken == tSYMBOL)
		return new SymbolExpr(current_pos(), gAtoms.add(st));

	lexpush();

	return constant();
}

Expr*
Parser::constant()
{
	cell val;
	char* st;
	int iToken = lex(&val, &st);
	auto pos = current_pos();

	switch(iToken)
	{
		case tNULL:
		{
			return new NullExpr(pos);
		}

		case tNUMBER:
		{
			return new NumberExpr(pos, val);
		}

		case tRATIONAL:
		{
			return new FloatExpr(pos, val);
		}

		case tSTRING:
		{
			return new StringExpr(pos, current_token()->str, current_token()->len);
		}

		case '{':
		{
			ArrayExpr* expr = new ArrayExpr(pos);

			do
			{
				Expr* child = hier14();
				expr->exprs().push_back(child);
			}
			while(matchtoken(','));

			if(!needtoken('}'))
			{
				lexclr(FALSE);
			}

			return expr;
		}

		default:
		{
			error_once(29);

			return new ErrorExpr();
		}
	}
}

CallExpr*
Parser::parse_call(const token_pos_t &Position, int iToken, Expr *pTarget)
{
	CallExpr *pCall = new CallExpr(Position, iToken, pTarget);

	if(matchtoken(')'))
	{
		return pCall;
	}

	bool bNamedParams = false;

	do
	{
		sp::Atom *pName = nullptr;

		if(matchtoken('.'))
		{
			bNamedParams = true;

			token_ident_t ident;

			if(!needsymbol(&ident))
			{
				break;
			}

			needtoken('=');

			pName = gAtoms.add(ident.name);
		}
		else
		{
			if(bNamedParams)
			{
				error_once(44);
			}
		}

		Expr *pExpr = nullptr;

		if(!matchtoken('_'))
		{
			pExpr = hier14();
		}

		pCall->args().emplace_back(pName, pExpr);

		if(matchtoken(')') || !needtoken(','))
		{
			break;
		}
	}
	while(freading && !matchtoken(tENDEXPR));

	return pCall;
}

Expr*
Parser::parse_view_as()
{
	auto pos = current_pos();

	needtoken('<');

	int tag = 0;
	{
		token_t iToken;

		lextok(&iToken);

		if(!parse_new_typename(&iToken, &tag))
		{
			tag = 0;
		}
	}
	needtoken('>');

	int paren = needtoken('(');

	Expr* expr = hier14();

	if(paren)
	{
		needtoken(')');
	}
	else
	{
		matchtoken(')');
	}

	return new CastExpr(pos, tVIEW_AS, tag, expr);
}

Expr*
Parser::struct_init()
{
	StructExpr* init = new StructExpr(current_pos());

	// '}' has already been lexed.
	do
	{
		sp::Atom* name = nullptr;

		token_ident_t ident;

		if(needsymbol(&ident))
		{
			name = gAtoms.add(ident.name);
		}

		needtoken('=');

		auto pos = current_pos();

		cell value;

		char* str;

		Expr* pExpr = nullptr;

		switch(lex(&value, &str))
		{
			case tSTRING:
			{
				pExpr = new StringExpr(pos, current_token()->str, current_token()->len);

				break;
			}
			case tNUMBER:
			{
				pExpr = new NumberExpr(pos, value);

				break;
			}
			case tRATIONAL:
			{
				pExpr = new FloatExpr(pos, value);

				break;
			}
			default:
			{
				error(1, "<constant value>", str);

				break;
			}
		}

		if(name && pExpr)
		{
			init->fields().push_back(StructInitField(name, pExpr));
		}
	}
	while(matchtoken(',') && !lexpeek('}'));

	needtoken('}');

	return init;
}
