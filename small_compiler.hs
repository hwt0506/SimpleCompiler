import Control.Applicative (Alternative, empty, (<|>))
import Control.Applicative (Alternative)
import qualified Control.Applicative
import Control.Monad
import qualified Control.Monad
import Data.Char --using ord,isAlpha,isDigit
--dont't ask me why these imports,all added by coming across errors
--backend,look easy to transform to C++
data Exp =  Constant Int     
           | Variable String
           | Plus Exp Exp     
           | Minus Exp Exp    
           | Greater Exp Exp
           | Less Exp Exp
           | Equal Exp Exp  
           | Times Exp Exp  
           | Div Exp Exp  
           deriving Show  --auto show function for print,yyds...
data Com =  Assign String Exp
           | Seq Com Com              
           | Cond Exp Com Com          
           | While Exp Com             
           | Declare String Exp Com   
           | Print Exp               
          deriving Show

type Location = Int
type Index = [String]
type Stack = [Int]   

position            :: String -> Index -> Location  
position name index = let 
                      pos n (nm:nms) = if name == nm
                                       then n
                                       else pos (n+1) nms  
        in pos 1 index

fetch            :: Location -> Stack -> Int
fetch n (v:vs)   =  if n == 1 then v else fetch (n-1) vs

put            :: Location -> Int -> Stack -> Stack
put n x (v:vs) = if n==1     
                 then x:vs 
                 else v:(put (n-1) x vs)

newtype M a =StOut(Stack -> (a, Stack, String)) 
instance Monad M where
    return x = StOut (\n-> (x,n, ""))
    e >>=  f = StOut (\n -> let  (a,n1,s1) = (unStOut e) n    
                                 (b,n2,s2) = unStOut (f a) n1
                          in (b,n2,s1++s2) )
unStOut (StOut f) = f

getfrom   :: Location ->M Int
getfrom i = StOut (\ns -> (fetch i ns, ns, ""))

write     :: Location -> Int -> M ()
write i v = StOut (\ns -> ( (), put i v ns, "") )

push :: Int -> M()
push x = StOut(\ns -> ((), x:ns, "") ) 

pop :: M ()
pop = StOut (\m -> let  (n:ns) = m    
                   in   ( () , ns ,"" )
            )
eval1           :: Exp -> Index -> M Int 
eval1 exp index = case exp of 
                    Constant n -> return n
                    Variable x -> let loc = position x index
                                    in getfrom loc
                    Minus x y  -> do { a <-eval1 x index ;
                                         b <-eval1 y index ;
                                         return (a-b) } 
                    Plus x y  -> do { a <-eval1 x index ;
                                         b <-eval1 y index ;
                                         return (a+b) } 
                    Greater x y -> do { a <-eval1 x index ;
                                         b <-eval1 y index ;
                                         return (if a > b
                                                 then 1 
                                                 else 0) }
                    Less x y -> do { a <-eval1 x index ;
                                         b <-eval1 y index ;
                                         return (if a < b
                                                 then 1 
                                                 else 0) }
                    Equal x y -> do { a <-eval1 x index ;
                                         b <-eval1 y index ;
                                         return (if a == b
                                                 then 1 
                                                 else 0) }
                    Times x y  -> do { a <-eval1 x index ;
                                         b <-eval1 y index ;
                                         return ( a * b )  }
                    Div x y  -> do { a <-eval1 x index ;
                                         b <-eval1 y index ;
                                         return ( div a b )  } 
--downfloor,or use fromIntegral to float

interpret1 :: Com -> Index -> M()
interpret1 stmt index = case stmt of
    Assign name e-> let loc = position name index
        in do { v <- eval1 e index ;
               write loc v }
    Seq s1 s2 -> do { x <- interpret1 s1 index ;
                      y <- interpret1 s2 index ;
                      return () }
    Cond e s1 s2 -> do { x <- eval1 e index ;
                            if x == 1
                            then interpret1 s1 index
                            else interpret1 s2 index }
    While e b -> let loop () = do { v <- eval1 e index ;
                                   if v==0 then return ()
                                   else do 
                                    {interpret1 b index ;
                                    loop () } }
                                in loop ()
    Declare nm e stmt -> do { v <- eval1 e index ;
                            push v ;
                            interpret1 stmt (nm:index) ;
                            pop }
    Print e -> do { v <- eval1 e index ;
                    output v}

output :: Show a => a -> M ()
output v = StOut (\n -> ((),n,show v))

--test a = unStOut (eval1 a []) []
interp a = unStOut (interpret1 a []) []

s1 = Declare "x" (Constant 150)
       (Declare "y" (Constant 200)
          (Seq (While (Greater (Variable "x" ) (Constant 0)
                      )
                      (Seq (Assign "x" (Minus (Variable "x")
                                              (Constant 1)
                                       )
                           )
                           (Assign "y" (Minus (Variable "y")
                                              (Constant 1)
                                       )
                           )
                      )
               )
               (Print (Variable "y"))
          )
       )

--frontend,the most simple one,sth like the dead parselib,no use of parsec...
newtype Parser a = Parser (String -> [(a,String)] )
instance Monad Parser where
   return a = Parser (\cs -> [(a,cs)] ) 
   p >>= f  = Parser (\cs ->  concat [ parse (f a) cs' 
                                        | (a,cs') <-parse p cs] )

item :: Parser Char
item = Parser (\xs -> case xs of 
                        ""     -> []
                        (c:cs) -> [ (c,cs) ]      )

instance MonadPlus Parser where
  mzero =  Parser (\cs -> [] )
  p `mplus` q = Parser (\cs -> parse p cs ++ parse q cs ) 

parse :: Parser a -> String -> [(a,String)]
--parse (Parser p) = p
parse (Parser p) inp               =  p inp

(+++)   :: Parser a -> Parser a -> Parser a
p +++ q = Parser (\cs -> case parse (p `mplus` q) cs of
                           [] -> []
                           (x:xs) -> [x]  )

sat :: (Char -> Bool) -> Parser Char
sat p = do { c <- item ; if p c then return c else mzero }

(?) :: Parser a -> ( a -> Bool) -> Parser a
p ? test = do { b <- p ; if test b then return b else mzero }

char :: Char -> Parser Char
char x = sat (\y -> x == y)

string :: String -> Parser String
string ""        = return ""
string (c:cs)    = do { char c ; string cs; return (c:cs)} 

lower :: Parser Char
lower = sat (\x -> 'a' <= x && x <= 'z')

upper :: Parser Char
upper = sat (\x -> 'A' <= x && x <= 'Z')

negs :: [Int] -> [Int]
negs xs = [x | x <- xs, x < 0]

many :: Parser a -> Parser [a]
many p = many1 p +++ return []
many1 :: Parser a -> Parser [a]
many1 p = do { a<-p ; as <- many p ;
return (a:as) }
--ignore space
space :: Parser String
space = many (sat isSpace)

token :: Parser a -> Parser a
token p = do { a<- p ; space ; return a}

symbol :: String -> Parser String
symbol cs = token (string cs)

apply :: Parser a -> String -> [(a,String)] 
apply p = parse (do {space ; p } ) 

ident :: Parser [Char]
ident = do { l   <- sat isAlpha ;
             lsc <- many (sat (\a -> isAlpha a || isDigit a)) ;
             return (l:lsc) }

identif :: Parser [Char]
identif = token ident

var :: Parser Exp
var = do { v <- identif ; return (Variable v) }

chainl :: Parser a -> Parser (a->a->a) -> a -> Parser a
chainl p op a = (p `chainl1` op) +++ return a 

chainl1 :: Parser a -> Parser (a->a->a) -> Parser a
p `chainl1` op = do { a <- p; rest a }
                 where 
                   rest a = (do  f <- op 
                                 b <- p
                                 rest (f a b) ) 
                            +++ return a

digit  :: Parser Exp 
digit  = do { x <- token (sat isDigit) ;
              return  (Constant ( ord x - ord '0' ) ) } 

digiti :: Parser Exp 
digiti = do{ p <- digit;
             l <- many digit;
             return( foldl (\a b -> let Constant nra = a
                                        Constant nrb = b
                                    in Constant  (10*nra + nrb)  ) 
                           (Constant 0)  
                           (p:l)             ) }

rexp  :: Parser Exp
rexp  = expr `chainl1` relop

expr :: Parser Exp
expr = term `chainl1` addop

term :: Parser Exp
term = factor `chainl1` mulop

factor :: Parser Exp
factor = var +++ 
         digiti +++
         do {  symbol "(" ; n <- rexp; symbol ")" ; return n }

addop :: Parser (Exp -> Exp -> Exp)       
addop = do { symbol "-" ; return (Minus) }  
        +++
        do { symbol "+" ; return (Plus) }

instance Fractional Int where
mulop :: Parser (Exp -> Exp -> Exp)                        
mulop = do { symbol "*" ; return (Times) } 
       +++
       do { symbol "/" ; return (Div) } 
        
relop :: Parser (Exp -> Exp -> Exp)                        
relop = do { symbol ">" ; return (Greater) } 
        +++
        do { symbol "<" ; return (Less) } 
        +++
        do { symbol "=" ; return (Equal) } 

--commands
printe :: Parser Com
printe = do { symbol "print" ; x <- rexp ; return (Print x) }

assign :: Parser Com
assign = do{x <- identif; symbol ":="; e <- rexp; return ( Assign x e)}

seqv  :: Parser Com
seqv = do { symbol "{" ; c <- com ; symbol ";"  ; d <- com ; symbol "}" 
            ; return (Seq c d) }

cond  :: Parser Com
cond  = do {  symbol "if"   ; e <- rexp ;
              symbol "then" ; c <- com ;
              symbol "else" ; d <- com ;
              return (Cond e c d) }

while  :: Parser Com
while = do { symbol "while" ;
             e <- rexp ;
             symbol "do" ;
             c <- com ;
             return (While e c)  }    

declare :: Parser Com
declare = do { symbol "declare" ;
               x <- identif ;
               symbol "=" ;
               e <- rexp  ;
               symbol "in" ;
               c <- com ;
               return  (Declare x e c ) }

com :: Parser Com
com = assign +++ seqv +++ cond +++ while +++ declare +++ printe  

--no one knows how much time I spent on test(do not support 过程性 language)...
eval2                          :: String -> Com
eval2 x                       =  case (parse (com) x) of
                                    [(n,[])]  -> n --just this one,much space wasted,ha
                                    []        -> error "invalid input"

main                          :: IO()
main                          =  do
                                     cal <- getLine;
                                     putStrLn (show(eval2( cal )))

-- left to be changed to teacher-wantted output...
--(stupid output,but I don't know how to find them in the process)