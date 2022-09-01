{-# OPTIONS_GHC -w #-}
module Parser where
import Ast
import Lexer
import qualified Control.Exception as Exc
import System.IO
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.0

data HappyAbsSyn t4 t5 t6 t7
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,223) ([8448,8738,241,17474,57924,29185,119,0,4360,35089,4103,8738,3858,17440,9284,16414,34952,15432,0,0,64,1,0,0,0,256,0,0,0,0,0,0,0,0,0,0,0,0,32768,0,0,0,0,128,0,16,0,4096,0,61152,2,0,0,0,0,0,49152,36863,15432,0,0,0,8737,61730,16896,17476,482,34948,50312,2051,4369,1929,8720,4642,8207,17476,7716,34880,18568,32828,4368,30865,8448,8738,241,0,0,0,0,0,0,0,49152,449,0,33664,3,0,1799,0,0,14,0,7184,0,8192,56,0,30584,0,0,0,0,8720,4642,8207,17476,7716,34880,18568,60,0,32,0,0,128,0,128,0,0,48,61152,128,49152,477,0,48000,19,0,0,0,4224,37137,120,0,0,1024,0,1,0,0,0,0,0,0,49152,16384,0,16,0,32768,0,0,1536,56320,285,0,0,0,0,0,0,4360,35089,7,0,4,0,32768,1,1911,4,0,0,0,0,640,16896,17476,482,30576,64,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_parser","Start","Decl","Expr","Type","\";\"","\"(\"","\")\"","\"+\"","\"-\"","\"*\"","\"~\"","\"=\"","\"<\"","\">\"","\"!\"","\"&&\"","\"||\"","\"^\"","\"if\"","\"then\"","\"else\"","\"fi\"","\"let\"","\":=\"","\"in\"","\"end\"","\"fn\"","\"::\"","\"->\"","\"fun\"","\"=>\"","\"int\"","\"bool\"","\"false\"","\"true\"","int","var","%eof"]
        bit_start = st Prelude.* 41
        bit_end = (st Prelude.+ 1) Prelude.* 41
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..40]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (9) = happyShift action_3
action_0 (14) = happyShift action_4
action_0 (18) = happyShift action_5
action_0 (22) = happyShift action_6
action_0 (26) = happyShift action_7
action_0 (30) = happyShift action_8
action_0 (33) = happyShift action_9
action_0 (37) = happyShift action_10
action_0 (38) = happyShift action_11
action_0 (39) = happyShift action_12
action_0 (40) = happyShift action_13
action_0 (4) = happyGoto action_14
action_0 (6) = happyGoto action_2
action_0 _ = happyFail (happyExpListPerState 0)

action_1 (9) = happyShift action_3
action_1 (14) = happyShift action_4
action_1 (18) = happyShift action_5
action_1 (22) = happyShift action_6
action_1 (26) = happyShift action_7
action_1 (30) = happyShift action_8
action_1 (33) = happyShift action_9
action_1 (37) = happyShift action_10
action_1 (38) = happyShift action_11
action_1 (39) = happyShift action_12
action_1 (40) = happyShift action_13
action_1 (6) = happyGoto action_2
action_1 _ = happyFail (happyExpListPerState 1)

action_2 (8) = happyShift action_23
action_2 (11) = happyShift action_24
action_2 (12) = happyShift action_25
action_2 (13) = happyShift action_26
action_2 (15) = happyShift action_27
action_2 (16) = happyShift action_28
action_2 (17) = happyShift action_29
action_2 (19) = happyShift action_30
action_2 (20) = happyShift action_31
action_2 (21) = happyShift action_32
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (9) = happyShift action_3
action_3 (14) = happyShift action_4
action_3 (18) = happyShift action_5
action_3 (22) = happyShift action_6
action_3 (26) = happyShift action_7
action_3 (30) = happyShift action_8
action_3 (33) = happyShift action_9
action_3 (37) = happyShift action_10
action_3 (38) = happyShift action_11
action_3 (39) = happyShift action_12
action_3 (40) = happyShift action_13
action_3 (6) = happyGoto action_22
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (9) = happyShift action_3
action_4 (14) = happyShift action_4
action_4 (18) = happyShift action_5
action_4 (22) = happyShift action_6
action_4 (26) = happyShift action_7
action_4 (30) = happyShift action_8
action_4 (33) = happyShift action_9
action_4 (37) = happyShift action_10
action_4 (38) = happyShift action_11
action_4 (39) = happyShift action_12
action_4 (40) = happyShift action_13
action_4 (6) = happyGoto action_21
action_4 _ = happyFail (happyExpListPerState 4)

action_5 (9) = happyShift action_3
action_5 (14) = happyShift action_4
action_5 (18) = happyShift action_5
action_5 (22) = happyShift action_6
action_5 (26) = happyShift action_7
action_5 (30) = happyShift action_8
action_5 (33) = happyShift action_9
action_5 (37) = happyShift action_10
action_5 (38) = happyShift action_11
action_5 (39) = happyShift action_12
action_5 (40) = happyShift action_13
action_5 (6) = happyGoto action_20
action_5 _ = happyFail (happyExpListPerState 5)

action_6 (9) = happyShift action_3
action_6 (14) = happyShift action_4
action_6 (18) = happyShift action_5
action_6 (22) = happyShift action_6
action_6 (26) = happyShift action_7
action_6 (30) = happyShift action_8
action_6 (33) = happyShift action_9
action_6 (37) = happyShift action_10
action_6 (38) = happyShift action_11
action_6 (39) = happyShift action_12
action_6 (40) = happyShift action_13
action_6 (6) = happyGoto action_19
action_6 _ = happyFail (happyExpListPerState 6)

action_7 (40) = happyShift action_18
action_7 (5) = happyGoto action_17
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (9) = happyShift action_16
action_8 _ = happyFail (happyExpListPerState 8)

action_9 (40) = happyShift action_15
action_9 _ = happyFail (happyExpListPerState 9)

action_10 _ = happyReduce_17

action_11 _ = happyReduce_18

action_12 _ = happyReduce_19

action_13 _ = happyReduce_20

action_14 (41) = happyAccept
action_14 _ = happyFail (happyExpListPerState 14)

action_15 (9) = happyShift action_48
action_15 _ = happyFail (happyExpListPerState 15)

action_16 (40) = happyShift action_47
action_16 _ = happyFail (happyExpListPerState 16)

action_17 (28) = happyShift action_46
action_17 _ = happyFail (happyExpListPerState 17)

action_18 (27) = happyShift action_45
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (11) = happyShift action_24
action_19 (12) = happyShift action_25
action_19 (13) = happyShift action_26
action_19 (15) = happyShift action_27
action_19 (16) = happyShift action_28
action_19 (17) = happyShift action_29
action_19 (19) = happyShift action_30
action_19 (20) = happyShift action_31
action_19 (21) = happyShift action_32
action_19 (23) = happyShift action_44
action_19 _ = happyFail (happyExpListPerState 19)

action_20 _ = happyReduce_11

action_21 _ = happyReduce_4

action_22 (9) = happyShift action_3
action_22 (10) = happyShift action_43
action_22 (11) = happyShift action_24
action_22 (12) = happyShift action_25
action_22 (13) = happyShift action_26
action_22 (14) = happyShift action_4
action_22 (15) = happyShift action_27
action_22 (16) = happyShift action_28
action_22 (17) = happyShift action_29
action_22 (18) = happyShift action_5
action_22 (19) = happyShift action_30
action_22 (20) = happyShift action_31
action_22 (21) = happyShift action_32
action_22 (22) = happyShift action_6
action_22 (26) = happyShift action_7
action_22 (30) = happyShift action_8
action_22 (33) = happyShift action_9
action_22 (37) = happyShift action_10
action_22 (38) = happyShift action_11
action_22 (39) = happyShift action_12
action_22 (40) = happyShift action_13
action_22 (6) = happyGoto action_42
action_22 _ = happyFail (happyExpListPerState 22)

action_23 _ = happyReduce_1

action_24 (9) = happyShift action_3
action_24 (14) = happyShift action_4
action_24 (18) = happyShift action_5
action_24 (22) = happyShift action_6
action_24 (26) = happyShift action_7
action_24 (30) = happyShift action_8
action_24 (33) = happyShift action_9
action_24 (37) = happyShift action_10
action_24 (38) = happyShift action_11
action_24 (39) = happyShift action_12
action_24 (40) = happyShift action_13
action_24 (6) = happyGoto action_41
action_24 _ = happyFail (happyExpListPerState 24)

action_25 (9) = happyShift action_3
action_25 (14) = happyShift action_4
action_25 (18) = happyShift action_5
action_25 (22) = happyShift action_6
action_25 (26) = happyShift action_7
action_25 (30) = happyShift action_8
action_25 (33) = happyShift action_9
action_25 (37) = happyShift action_10
action_25 (38) = happyShift action_11
action_25 (39) = happyShift action_12
action_25 (40) = happyShift action_13
action_25 (6) = happyGoto action_40
action_25 _ = happyFail (happyExpListPerState 25)

action_26 (9) = happyShift action_3
action_26 (14) = happyShift action_4
action_26 (18) = happyShift action_5
action_26 (22) = happyShift action_6
action_26 (26) = happyShift action_7
action_26 (30) = happyShift action_8
action_26 (33) = happyShift action_9
action_26 (37) = happyShift action_10
action_26 (38) = happyShift action_11
action_26 (39) = happyShift action_12
action_26 (40) = happyShift action_13
action_26 (6) = happyGoto action_39
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (9) = happyShift action_3
action_27 (14) = happyShift action_4
action_27 (18) = happyShift action_5
action_27 (22) = happyShift action_6
action_27 (26) = happyShift action_7
action_27 (30) = happyShift action_8
action_27 (33) = happyShift action_9
action_27 (37) = happyShift action_10
action_27 (38) = happyShift action_11
action_27 (39) = happyShift action_12
action_27 (40) = happyShift action_13
action_27 (6) = happyGoto action_38
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (9) = happyShift action_3
action_28 (14) = happyShift action_4
action_28 (18) = happyShift action_5
action_28 (22) = happyShift action_6
action_28 (26) = happyShift action_7
action_28 (30) = happyShift action_8
action_28 (33) = happyShift action_9
action_28 (37) = happyShift action_10
action_28 (38) = happyShift action_11
action_28 (39) = happyShift action_12
action_28 (40) = happyShift action_13
action_28 (6) = happyGoto action_37
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (9) = happyShift action_3
action_29 (14) = happyShift action_4
action_29 (18) = happyShift action_5
action_29 (22) = happyShift action_6
action_29 (26) = happyShift action_7
action_29 (30) = happyShift action_8
action_29 (33) = happyShift action_9
action_29 (37) = happyShift action_10
action_29 (38) = happyShift action_11
action_29 (39) = happyShift action_12
action_29 (40) = happyShift action_13
action_29 (6) = happyGoto action_36
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (9) = happyShift action_3
action_30 (14) = happyShift action_4
action_30 (18) = happyShift action_5
action_30 (22) = happyShift action_6
action_30 (26) = happyShift action_7
action_30 (30) = happyShift action_8
action_30 (33) = happyShift action_9
action_30 (37) = happyShift action_10
action_30 (38) = happyShift action_11
action_30 (39) = happyShift action_12
action_30 (40) = happyShift action_13
action_30 (6) = happyGoto action_35
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (9) = happyShift action_3
action_31 (14) = happyShift action_4
action_31 (18) = happyShift action_5
action_31 (22) = happyShift action_6
action_31 (26) = happyShift action_7
action_31 (30) = happyShift action_8
action_31 (33) = happyShift action_9
action_31 (37) = happyShift action_10
action_31 (38) = happyShift action_11
action_31 (39) = happyShift action_12
action_31 (40) = happyShift action_13
action_31 (6) = happyGoto action_34
action_31 _ = happyFail (happyExpListPerState 31)

action_32 (9) = happyShift action_3
action_32 (14) = happyShift action_4
action_32 (18) = happyShift action_5
action_32 (22) = happyShift action_6
action_32 (26) = happyShift action_7
action_32 (30) = happyShift action_8
action_32 (33) = happyShift action_9
action_32 (37) = happyShift action_10
action_32 (38) = happyShift action_11
action_32 (39) = happyShift action_12
action_32 (40) = happyShift action_13
action_32 (6) = happyGoto action_33
action_32 _ = happyFail (happyExpListPerState 32)

action_33 _ = happyReduce_14

action_34 _ = happyReduce_13

action_35 _ = happyReduce_12

action_36 (11) = happyShift action_24
action_36 (12) = happyShift action_25
action_36 (13) = happyShift action_26
action_36 (15) = happyFail []
action_36 (16) = happyFail []
action_36 (17) = happyFail []
action_36 (19) = happyShift action_30
action_36 (20) = happyShift action_31
action_36 (21) = happyShift action_32
action_36 _ = happyReduce_10

action_37 (11) = happyShift action_24
action_37 (12) = happyShift action_25
action_37 (13) = happyShift action_26
action_37 (15) = happyFail []
action_37 (16) = happyFail []
action_37 (17) = happyFail []
action_37 (19) = happyShift action_30
action_37 (20) = happyShift action_31
action_37 (21) = happyShift action_32
action_37 _ = happyReduce_9

action_38 (11) = happyShift action_24
action_38 (12) = happyShift action_25
action_38 (13) = happyShift action_26
action_38 (15) = happyFail []
action_38 (16) = happyFail []
action_38 (17) = happyFail []
action_38 (19) = happyShift action_30
action_38 (20) = happyShift action_31
action_38 (21) = happyShift action_32
action_38 _ = happyReduce_8

action_39 (19) = happyShift action_30
action_39 (20) = happyShift action_31
action_39 (21) = happyShift action_32
action_39 _ = happyReduce_7

action_40 (13) = happyShift action_26
action_40 (19) = happyShift action_30
action_40 (20) = happyShift action_31
action_40 (21) = happyShift action_32
action_40 _ = happyReduce_6

action_41 (13) = happyShift action_26
action_41 (19) = happyShift action_30
action_41 (20) = happyShift action_31
action_41 (21) = happyShift action_32
action_41 _ = happyReduce_5

action_42 (10) = happyShift action_54
action_42 (11) = happyShift action_24
action_42 (12) = happyShift action_25
action_42 (13) = happyShift action_26
action_42 (15) = happyShift action_27
action_42 (16) = happyShift action_28
action_42 (17) = happyShift action_29
action_42 (19) = happyShift action_30
action_42 (20) = happyShift action_31
action_42 (21) = happyShift action_32
action_42 _ = happyFail (happyExpListPerState 42)

action_43 _ = happyReduce_3

action_44 (9) = happyShift action_3
action_44 (14) = happyShift action_4
action_44 (18) = happyShift action_5
action_44 (22) = happyShift action_6
action_44 (26) = happyShift action_7
action_44 (30) = happyShift action_8
action_44 (33) = happyShift action_9
action_44 (37) = happyShift action_10
action_44 (38) = happyShift action_11
action_44 (39) = happyShift action_12
action_44 (40) = happyShift action_13
action_44 (6) = happyGoto action_53
action_44 _ = happyFail (happyExpListPerState 44)

action_45 (9) = happyShift action_3
action_45 (14) = happyShift action_4
action_45 (18) = happyShift action_5
action_45 (22) = happyShift action_6
action_45 (26) = happyShift action_7
action_45 (30) = happyShift action_8
action_45 (33) = happyShift action_9
action_45 (37) = happyShift action_10
action_45 (38) = happyShift action_11
action_45 (39) = happyShift action_12
action_45 (40) = happyShift action_13
action_45 (6) = happyGoto action_52
action_45 _ = happyFail (happyExpListPerState 45)

action_46 (9) = happyShift action_3
action_46 (14) = happyShift action_4
action_46 (18) = happyShift action_5
action_46 (22) = happyShift action_6
action_46 (26) = happyShift action_7
action_46 (30) = happyShift action_8
action_46 (33) = happyShift action_9
action_46 (37) = happyShift action_10
action_46 (38) = happyShift action_11
action_46 (39) = happyShift action_12
action_46 (40) = happyShift action_13
action_46 (6) = happyGoto action_51
action_46 _ = happyFail (happyExpListPerState 46)

action_47 (31) = happyShift action_50
action_47 _ = happyFail (happyExpListPerState 47)

action_48 (40) = happyShift action_49
action_48 _ = happyFail (happyExpListPerState 48)

action_49 (31) = happyShift action_60
action_49 _ = happyFail (happyExpListPerState 49)

action_50 (35) = happyShift action_58
action_50 (36) = happyShift action_59
action_50 (7) = happyGoto action_57
action_50 _ = happyFail (happyExpListPerState 50)

action_51 (11) = happyShift action_24
action_51 (12) = happyShift action_25
action_51 (13) = happyShift action_26
action_51 (15) = happyShift action_27
action_51 (16) = happyShift action_28
action_51 (17) = happyShift action_29
action_51 (19) = happyShift action_30
action_51 (20) = happyShift action_31
action_51 (21) = happyShift action_32
action_51 (29) = happyShift action_56
action_51 _ = happyFail (happyExpListPerState 51)

action_52 (11) = happyShift action_24
action_52 (12) = happyShift action_25
action_52 (13) = happyShift action_26
action_52 (15) = happyShift action_27
action_52 (16) = happyShift action_28
action_52 (17) = happyShift action_29
action_52 (19) = happyShift action_30
action_52 (20) = happyShift action_31
action_52 (21) = happyShift action_32
action_52 _ = happyReduce_2

action_53 (11) = happyShift action_24
action_53 (12) = happyShift action_25
action_53 (13) = happyShift action_26
action_53 (15) = happyShift action_27
action_53 (16) = happyShift action_28
action_53 (17) = happyShift action_29
action_53 (19) = happyShift action_30
action_53 (20) = happyShift action_31
action_53 (21) = happyShift action_32
action_53 (24) = happyShift action_55
action_53 _ = happyFail (happyExpListPerState 53)

action_54 _ = happyReduce_21

action_55 (9) = happyShift action_3
action_55 (14) = happyShift action_4
action_55 (18) = happyShift action_5
action_55 (22) = happyShift action_6
action_55 (26) = happyShift action_7
action_55 (30) = happyShift action_8
action_55 (33) = happyShift action_9
action_55 (37) = happyShift action_10
action_55 (38) = happyShift action_11
action_55 (39) = happyShift action_12
action_55 (40) = happyShift action_13
action_55 (6) = happyGoto action_64
action_55 _ = happyFail (happyExpListPerState 55)

action_56 _ = happyReduce_15

action_57 (10) = happyShift action_62
action_57 (32) = happyShift action_63
action_57 _ = happyFail (happyExpListPerState 57)

action_58 _ = happyReduce_25

action_59 _ = happyReduce_26

action_60 (35) = happyShift action_58
action_60 (36) = happyShift action_59
action_60 (7) = happyGoto action_61
action_60 _ = happyFail (happyExpListPerState 60)

action_61 (10) = happyShift action_68
action_61 (32) = happyShift action_63
action_61 _ = happyFail (happyExpListPerState 61)

action_62 (34) = happyShift action_67
action_62 _ = happyFail (happyExpListPerState 62)

action_63 (35) = happyShift action_58
action_63 (36) = happyShift action_59
action_63 (7) = happyGoto action_66
action_63 _ = happyFail (happyExpListPerState 63)

action_64 (11) = happyShift action_24
action_64 (12) = happyShift action_25
action_64 (13) = happyShift action_26
action_64 (15) = happyShift action_27
action_64 (16) = happyShift action_28
action_64 (17) = happyShift action_29
action_64 (19) = happyShift action_30
action_64 (20) = happyShift action_31
action_64 (21) = happyShift action_32
action_64 (25) = happyShift action_65
action_64 _ = happyFail (happyExpListPerState 64)

action_65 _ = happyReduce_16

action_66 (32) = happyShift action_63
action_66 _ = happyReduce_24

action_67 (9) = happyShift action_3
action_67 (14) = happyShift action_4
action_67 (18) = happyShift action_5
action_67 (22) = happyShift action_6
action_67 (26) = happyShift action_7
action_67 (30) = happyShift action_8
action_67 (33) = happyShift action_9
action_67 (37) = happyShift action_10
action_67 (38) = happyShift action_11
action_67 (39) = happyShift action_12
action_67 (40) = happyShift action_13
action_67 (6) = happyGoto action_70
action_67 _ = happyFail (happyExpListPerState 67)

action_68 (31) = happyShift action_69
action_68 _ = happyFail (happyExpListPerState 68)

action_69 (35) = happyShift action_58
action_69 (36) = happyShift action_59
action_69 (7) = happyGoto action_72
action_69 _ = happyFail (happyExpListPerState 69)

action_70 (11) = happyShift action_24
action_70 (12) = happyShift action_25
action_70 (13) = happyShift action_26
action_70 (15) = happyShift action_27
action_70 (16) = happyShift action_28
action_70 (17) = happyShift action_29
action_70 (19) = happyShift action_30
action_70 (20) = happyShift action_31
action_70 (21) = happyShift action_32
action_70 (29) = happyShift action_71
action_70 _ = happyFail (happyExpListPerState 70)

action_71 _ = happyReduce_22

action_72 (32) = happyShift action_63
action_72 (34) = happyShift action_73
action_72 _ = happyFail (happyExpListPerState 72)

action_73 (9) = happyShift action_3
action_73 (14) = happyShift action_4
action_73 (18) = happyShift action_5
action_73 (22) = happyShift action_6
action_73 (26) = happyShift action_7
action_73 (30) = happyShift action_8
action_73 (33) = happyShift action_9
action_73 (37) = happyShift action_10
action_73 (38) = happyShift action_11
action_73 (39) = happyShift action_12
action_73 (40) = happyShift action_13
action_73 (6) = happyGoto action_74
action_73 _ = happyFail (happyExpListPerState 73)

action_74 (11) = happyShift action_24
action_74 (12) = happyShift action_25
action_74 (13) = happyShift action_26
action_74 (15) = happyShift action_27
action_74 (16) = happyShift action_28
action_74 (17) = happyShift action_29
action_74 (19) = happyShift action_30
action_74 (20) = happyShift action_31
action_74 (21) = happyShift action_32
action_74 (29) = happyShift action_75
action_74 _ = happyFail (happyExpListPerState 74)

action_75 _ = happyReduce_23

happyReduce_1 = happySpecReduce_2  4 happyReduction_1
happyReduction_1 _
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn4
		 (happy_var_1
	)
happyReduction_1 _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_3  5 happyReduction_2
happyReduction_2 (HappyAbsSyn6  happy_var_3)
	_
	(HappyTerminal (ID happy_var_1))
	 =  HappyAbsSyn5
		 (Decl happy_var_1 happy_var_3
	)
happyReduction_2 _ _ _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_3  6 happyReduction_3
happyReduction_3 _
	(HappyAbsSyn6  happy_var_2)
	_
	 =  HappyAbsSyn6
		 (happy_var_2
	)
happyReduction_3 _ _ _  = notHappyAtAll 

happyReduce_4 = happySpecReduce_2  6 happyReduction_4
happyReduction_4 (HappyAbsSyn6  happy_var_2)
	_
	 =  HappyAbsSyn6
		 (UnExpr Negate happy_var_2
	)
happyReduction_4 _ _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_3  6 happyReduction_5
happyReduction_5 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (BinExpr Plus happy_var_1 happy_var_3
	)
happyReduction_5 _ _ _  = notHappyAtAll 

happyReduce_6 = happySpecReduce_3  6 happyReduction_6
happyReduction_6 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (BinExpr Minus happy_var_1 happy_var_3
	)
happyReduction_6 _ _ _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_3  6 happyReduction_7
happyReduction_7 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (BinExpr Times happy_var_1 happy_var_3
	)
happyReduction_7 _ _ _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_3  6 happyReduction_8
happyReduction_8 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (BinExpr Equals happy_var_1 happy_var_3
	)
happyReduction_8 _ _ _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_3  6 happyReduction_9
happyReduction_9 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (BinExpr LessThan happy_var_1 happy_var_3
	)
happyReduction_9 _ _ _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_3  6 happyReduction_10
happyReduction_10 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (BinExpr GreaterThan happy_var_1 happy_var_3
	)
happyReduction_10 _ _ _  = notHappyAtAll 

happyReduce_11 = happySpecReduce_2  6 happyReduction_11
happyReduction_11 (HappyAbsSyn6  happy_var_2)
	_
	 =  HappyAbsSyn6
		 (UnExpr Not happy_var_2
	)
happyReduction_11 _ _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_3  6 happyReduction_12
happyReduction_12 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (BinExpr And happy_var_1 happy_var_3
	)
happyReduction_12 _ _ _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_3  6 happyReduction_13
happyReduction_13 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (BinExpr Or happy_var_1 happy_var_3
	)
happyReduction_13 _ _ _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_3  6 happyReduction_14
happyReduction_14 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn6
		 (BinExpr Xor happy_var_1 happy_var_3
	)
happyReduction_14 _ _ _  = notHappyAtAll 

happyReduce_15 = happyReduce 5 6 happyReduction_15
happyReduction_15 (_ `HappyStk`
	(HappyAbsSyn6  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn5  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (Let happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_16 = happyReduce 7 6 happyReduction_16
happyReduction_16 (_ `HappyStk`
	(HappyAbsSyn6  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (Ite happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_17 = happySpecReduce_1  6 happyReduction_17
happyReduction_17 _
	 =  HappyAbsSyn6
		 (BoolConst False
	)

happyReduce_18 = happySpecReduce_1  6 happyReduction_18
happyReduction_18 _
	 =  HappyAbsSyn6
		 (BoolConst True
	)

happyReduce_19 = happySpecReduce_1  6 happyReduction_19
happyReduction_19 (HappyTerminal (CONST happy_var_1))
	 =  HappyAbsSyn6
		 (IntConst happy_var_1
	)
happyReduction_19 _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  6 happyReduction_20
happyReduction_20 (HappyTerminal (ID happy_var_1))
	 =  HappyAbsSyn6
		 (VarExpr happy_var_1
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happyReduce 4 6 happyReduction_21
happyReduction_21 (_ `HappyStk`
	(HappyAbsSyn6  happy_var_3) `HappyStk`
	(HappyAbsSyn6  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (AppExp happy_var_2 happy_var_3
	) `HappyStk` happyRest

happyReduce_22 = happyReduce 9 6 happyReduction_22
happyReduction_22 (_ `HappyStk`
	(HappyAbsSyn6  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (ID happy_var_3)) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (Fn happy_var_3 happy_var_5 happy_var_8
	) `HappyStk` happyRest

happyReduce_23 = happyReduce 12 6 happyReduction_23
happyReduction_23 (_ `HappyStk`
	(HappyAbsSyn6  happy_var_11) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_9) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (ID happy_var_4)) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (ID happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (FunExp happy_var_2 happy_var_4 happy_var_6 happy_var_9 happy_var_11
	) `HappyStk` happyRest

happyReduce_24 = happySpecReduce_3  7 happyReduction_24
happyReduction_24 (HappyAbsSyn7  happy_var_3)
	_
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn7
		 (Arrow happy_var_1 happy_var_3
	)
happyReduction_24 _ _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_1  7 happyReduction_25
happyReduction_25 _
	 =  HappyAbsSyn7
		 (IntType
	)

happyReduce_26 = happySpecReduce_1  7 happyReduction_26
happyReduction_26 _
	 =  HappyAbsSyn7
		 (BoolType
	)

happyNewToken action sts stk [] =
	action 41 41 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	EOF happy_dollar_dollar -> cont 8;
	LPAREN happy_dollar_dollar -> cont 9;
	RPAREN happy_dollar_dollar -> cont 10;
	PLUS happy_dollar_dollar -> cont 11;
	MINUS happy_dollar_dollar -> cont 12;
	TIMES happy_dollar_dollar -> cont 13;
	NEGATE happy_dollar_dollar -> cont 14;
	EQUALS happy_dollar_dollar -> cont 15;
	LESSTHAN happy_dollar_dollar -> cont 16;
	GREATERTHAN happy_dollar_dollar -> cont 17;
	NOT happy_dollar_dollar -> cont 18;
	AND happy_dollar_dollar -> cont 19;
	OR happy_dollar_dollar -> cont 20;
	XOR happy_dollar_dollar -> cont 21;
	IF happy_dollar_dollar -> cont 22;
	THEN happy_dollar_dollar -> cont 23;
	ELSE happy_dollar_dollar -> cont 24;
	FI happy_dollar_dollar -> cont 25;
	LET happy_dollar_dollar -> cont 26;
	ASSIGN happy_dollar_dollar -> cont 27;
	IN happy_dollar_dollar -> cont 28;
	END happy_dollar_dollar -> cont 29;
	FN happy_dollar_dollar -> cont 30;
	COLON happy_dollar_dollar -> cont 31;
	RIGHTARROW happy_dollar_dollar -> cont 32;
	FUN happy_dollar_dollar -> cont 33;
	IMPLY happy_dollar_dollar -> cont 34;
	INT happy_dollar_dollar -> cont 35;
	BOOL happy_dollar_dollar -> cont 36;
	FALSE happy_dollar_dollar -> cont 37;
	TRUE happy_dollar_dollar -> cont 38;
	CONST happy_dollar_dollar -> cont 39;
	ID happy_dollar_dollar -> cont 40;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 41 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Prelude.Functor HappyIdentity where
    fmap f (HappyIdentity a) = HappyIdentity (f a)

instance Applicative HappyIdentity where
    pure  = HappyIdentity
    (<*>) = ap
instance Prelude.Monad HappyIdentity where
    return = pure
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (Prelude.>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (Prelude.return)
happyThen1 m k tks = (Prelude.>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (Prelude.return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> HappyIdentity a
happyError' = HappyIdentity Prelude.. (\(tokens, _) -> parseError tokens)
parser tks = happyRunIdentity happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError [] = error $ "Syntax Error in the last token"
parseError (x:xs) = error $ "Syntax Error: " ++ (show x)

preOrder :: Expr -> [String]
preOrder exp =
    case exp of
                BoolConst True -> ["BoolConst" ++ " " ++ "True"]
                BoolConst False -> ["BoolConst" ++ " " ++ "False"]
                VarExpr s -> ["VarExpr" ++ " " ++  s]
                IntConst n -> ["IntConst" ++ " " ++ show n]
                UnExpr Negate exp' -> "Negate":preOrder exp'
                UnExpr Not exp' -> "Not":preOrder exp'
                BinExpr Plus exp' exp'' -> "Plus":preOrder exp'++preOrder exp''
                BinExpr Minus exp' exp'' -> "Minus":preOrder exp'++preOrder exp''
                BinExpr Times exp' exp'' -> "Times":preOrder exp'++preOrder exp''
                BinExpr And exp' exp'' -> "And":preOrder exp'++preOrder exp''
                BinExpr Or exp' exp'' -> "Or":preOrder exp'++preOrder exp''
                BinExpr Xor exp' exp'' -> "Xor":preOrder exp'++preOrder exp''
            --    Implies exp' exp'' -> "Implies":preOrder exp'++preOrder exp''
                BinExpr Equals exp' exp'' -> "Equals":preOrder exp'++preOrder exp''
                BinExpr GreaterThan exp' exp'' -> "GrThan":preOrder exp'++preOrder exp''
                BinExpr LessThan exp' exp'' -> "LessThan":preOrder exp'++preOrder exp''
                Let (Decl s exp') exp'' -> "Let":["VarExpr" ++ " " ++ s] ++preOrder exp'++preOrder exp''
                Ite exp' exp'' exp''' -> "Ite":preOrder exp'++preOrder exp''++preOrder exp'''
                AppExp exp' exp'' -> "AppExp":preOrder exp'++preOrder exp''
                Fn s _ exp' -> "Fn":["VarExpr" ++ " " ++ s]++preOrder exp'
                FunExp name y _ _ exp' -> "Fun":["VarExpr" ++ name]++["VarExpr" ++ y]++preOrder exp'

preOrderAST :: FilePath -> IO ()
preOrderAST path = do
    s <- readFile path
    tkls <- Exc.try (return (scanTokens s))
    case tkls of
        Left e -> do putStrLn (show (e::Exc.SomeException))
        Right ts ->
            do 
                exp <- Exc.try (return (parser ts))
                case exp of 
                    Left e -> do putStrLn (show (e::Exc.SomeException))
                    Right expr -> do print (preOrder expr)
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Prelude.Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x Prelude.< y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `Prelude.div` 16)) (bit `Prelude.mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Prelude.Int ->                    -- token number
         Prelude.Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Prelude.- ((1) :: Prelude.Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Prelude.Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n Prelude.- ((1) :: Prelude.Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Prelude.- ((1)::Prelude.Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
