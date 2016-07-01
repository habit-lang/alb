{-# LANGUAGE DeriveDataTypeable #-}
module Fidget.AST where

import Data.Generics
import Data.Int (Int32)
import qualified Syntax.Common

-- A Haskell rendering of official Fidget syntax in /compcert-hasp/gcfrontend/Fidget.v

type Id = Syntax.Common.Id -- actually positive in Compcert-land, if we care

type Nat = Integer -- non-negative, in case we care

type Machint = Int32 {- 32-bit machine integers -}
type Machfloat = Double {- 64-bit IEEE floats -}

type Tcon = Id

data Area =
    Stored Ftyp {- probably only Fint, Fidx, Fref supported -}
  | Array Area Nat 
  | Struct Id
  deriving (Eq, Typeable, Data)

data Ftyp =
    Funit {- introduced with audited-op return types or Cunit; eliminated with let -}
  | Fint {- 32 bits -}
  | Ftcon Tcon 
  | Frecordt Tcon Nat {- parent tc, tag -}
  | Ffun [Ftyp] Ftyp {- args, res -}
  | Fix Machint {- Introduced with ModIx and Relax. Eliminated with @ and Relax and more. -}
  | Fnzero {- Non-zero integer -}
  | Fref Area {- Introduced via variables with names that appear in the AreaMap. Eliminated with readRef/writeRef. -}
  | Fptr Area {- Potentially null pointer to area -}
  deriving (Eq, Typeable, Data)

{- FUnsigned = Fint32 -}

data Fsignature =
  Fsignature [Ftyp] Ftyp  {- args, result; void functions return result type Unit -}
  deriving (Eq, Typeable, Data)

data Unary_operation =
    Ocast8unsigned        {- 8-bit zero extension  -}
  | Ocast8signed          {- 8-bit sign extension  -}
  | Ocast16unsigned       {- 16-bit zero extension  -}
  | Ocast16signed         {- 16-bit sign extension -}
  | Onegint               {- integer opposite -}
  | Onotbool              {- boolean negation  -}
  | Onotint               {- bitwise complement  -}
  | Orelax Machint Machint{- cast Fix n to Fix m for m >= n -}
  | Oixunsigned Machint   {- cast Fix n to Fint -}
  | Omodix Machint        {- coerce Fint to Fix n -}
  | Onzunsigned           {- cast Fnzero to Fint -}
  | Optr                  {- cast (Fref a) to (Fptr a) -}
  deriving (Eq, Typeable, Data)

data Comparison =
    Ceq              {- same -}
  | Cne               {- different -}
  | Clt                {- less than -}
  | Cle               {- less than or equal -}
  | Cgt                {- greater than -}
  | Cge               {- greater than or equal -}
  deriving (Eq, Typeable, Data)

data Binary_operation =
    Oadd                 {- integer addition -}
  | Osub                 {- integer subtraction -}
  | Omul                 {- integer multiplication -}
  | Odiv                 {- integer signed division -}
  | Odivu                {- integer unsigned division -}
  | Omod                 {- integer signed modulus -}
  | Omodu                {- integer unsigned modulus -}
  | Oand                 {- bitwise ``and'' -}
  | Oor                  {- bitwise ``or'' -}
  | Oxor                 {- bitwise ``xor'' -}
  | Oshl                 {- left shift -}
  | Oshr                 {- right signed shift -}
  | Oshru                {- right unsigned shift -}
  | Ocmp Comparison    {- integer signed comparison -}
  | Ocmpu Comparison  {- integer unsigned comparison -}
--   | Oixleq Machint    {- integer vs. Fix n unsigned leq -} 
  deriving (Eq, Typeable, Data)

data Constant =
    Ounit 
  | Ointconst Machint
  | Oarea Id Area 
  deriving (Eq, Typeable, Data)

data Atom = 
    Agvar Id Ftyp
  | Avar Id Ftyp
  | Aconst Constant 
  | Aload Atom Nat Ftyp
  | Aat Atom Atom Area
  | Asel Atom Nat Area
  | Aunop Unary_operation Atom
  | Abinop Binary_operation Atom Atom
  deriving (Eq, Typeable, Data)

data SimplExpr =
    Satom Atom
  | Scall Fsignature Id [Atom] {- calls to known (a.k.a. top-level) functions -}
  | Sapp Fsignature Atom [Atom] {- closure applications -}
  | Salloc Tcon Nat [Atom]
  deriving (Eq, Typeable, Data)

type Label = Id

data Expr =
    Eatom Atom
  | Elet Id Ftyp SimplExpr Expr
  | Eletrec [(Id,Function)] Expr 
  | Eifthenelse Atom Expr Expr {- what is type of atom? -}
  | Ecase Atom [(Id,Nat,Expr)] (Maybe (Id,Expr)) {- arms are labeled with (tcon,tag); maybe is default -}
  | Eixcase Atom Machint Id Expr Expr {- scrutinee must have type Fint;
                                         id gets type (Fidx n) in fourth arg if Machint is n -}
  | Enzcase Atom         Id Expr Expr {- scrutinee must have type Fint;
                                         id gets type Fnzero in fourth arg  -}
  | Erefcase Atom Area   Id Expr Expr {- scrutinee must have type (Fptr a)
                                         id gets type (Fref a) in fourth arg  -}
  | Eerror Ftyp 
  | Eletlabel [(Label,Function)] Expr {- label with typed args -}
  | Egoto Label [Atom] Ftyp           {- jump to label with actual args; type is as for Eerror -}
  deriving (Eq, Typeable, Data)

data Function = Function [(Id,Ftyp)] Ftyp Expr 
  deriving (Eq, Typeable, Data)

data Fundec = 
    Internal Function
  | External ExternalFunction
  deriving (Eq, Typeable, Data)

data ExternalFunction =
    EFexternal String CMSignature
  | EFbuiltin String CMSignature
  | EFvload MemoryChunk
  | EFvstore MemoryChunk
  | EFmemcpy Int {-size-} Int {-alignment-}
  deriving (Eq, Typeable, Data)

data MemoryChunk =
    MCint8signed
  | MCint8unsigned
  | MCint16signed
  | MCint16unsigned
  | MCint32
  | MCfloat32
  | MCfloat64
  deriving (Eq, Typeable, Data)

data CMSignature = CMSig [CMTyp] (Maybe CMTyp)
  deriving (Eq, Typeable, Data)

data CMTyp =
    CMInt
  | CMFloat
  deriving (Eq, Typeable, Data)

data StructDesc =
  StructDesc Nat [(Nat,Area)] -- total width (bytes),  mapping from offset (bytes) to area 
  deriving (Eq, Typeable, Data)

data Volatility = Volatile | Nonvolatile
  deriving (Eq, Typeable, Data)

data Global = Global Ftyp Expr
  deriving (Eq, Typeable, Data)

data Program =
  Program
    [(Id,Global)] -- globals
    [(Id,Fundec)] -- functions
    Id -- main
    Id -- initialization function
    [(Id,[[Ftyp]])]  -- tconenv: field types for each small-natural tag, for each tcon
    [(Id,Area,Volatility,Int{-size in bytes-})]
    [(Id,StructDesc)]
  deriving (Eq, Typeable, Data)
