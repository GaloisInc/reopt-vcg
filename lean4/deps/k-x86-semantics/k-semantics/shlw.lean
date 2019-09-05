def shlw1 : instruction :=
  definst "shlw" $ do
    pattern fun cl (v_2866 : reg (bv 16)) => do
      v_4974 <- getRegister rcx;
      v_4976 <- eval (bv_and (extract v_4974 56 64) (expression.bv_nat 8 31));
      v_4977 <- eval (eq v_4976 (expression.bv_nat 8 0));
      v_4978 <- eval (notBool_ v_4977);
      v_4979 <- getRegister v_2866;
      v_4983 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4979) (concat (expression.bv_nat 9 0) v_4976)) 0 17);
      v_4984 <- eval (extract v_4983 1 17);
      v_4987 <- getRegister zf;
      v_4991 <- eval (isBitSet v_4983 1);
      v_4993 <- getRegister sf;
      v_5000 <- getRegister pf;
      v_5004 <- eval (eq v_4976 (expression.bv_nat 8 1));
      v_5005 <- eval (uge v_4976 (expression.bv_nat 8 16));
      v_5010 <- getRegister cf;
      v_5015 <- eval (bit_or (bit_and v_5005 undef) (bit_and (notBool_ v_5005) (bit_or (bit_and v_4978 (isBitSet v_4983 0)) (bit_and v_4977 (eq v_5010 (expression.bv_nat 1 1))))));
      v_5020 <- eval (bit_and v_4978 undef);
      v_5021 <- getRegister of;
      v_5027 <- getRegister af;
      setRegister (lhs.of_reg v_2866) v_4984;
      setRegister af (bit_or v_5020 (bit_and v_4977 (eq v_5027 (expression.bv_nat 1 1))));
      setRegister cf v_5015;
      setRegister of (bit_or (bit_and v_5004 (notBool_ (eq v_5015 v_4991))) (bit_and (notBool_ v_5004) (bit_or v_5020 (bit_and v_4977 (eq v_5021 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_4978 (parityFlag (extract v_4983 9 17))) (bit_and v_4977 (eq v_5000 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_4978 v_4991) (bit_and v_4977 (eq v_4993 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_4978 (eq v_4984 (expression.bv_nat 16 0))) (bit_and v_4977 (eq v_4987 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2869 : imm int) (v_2871 : reg (bv 16)) => do
      v_5039 <- eval (bv_and (handleImmediateWithSignExtend v_2869 8 8) (expression.bv_nat 8 31));
      v_5040 <- eval (eq v_5039 (expression.bv_nat 8 0));
      v_5041 <- eval (notBool_ v_5040);
      v_5042 <- getRegister v_2871;
      v_5046 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5042) (concat (expression.bv_nat 9 0) v_5039)) 0 17);
      v_5047 <- eval (extract v_5046 1 17);
      v_5050 <- getRegister zf;
      v_5054 <- eval (isBitSet v_5046 1);
      v_5056 <- getRegister sf;
      v_5063 <- getRegister pf;
      v_5067 <- eval (eq v_5039 (expression.bv_nat 8 1));
      v_5068 <- eval (uge v_5039 (expression.bv_nat 8 16));
      v_5073 <- getRegister cf;
      v_5078 <- eval (bit_or (bit_and v_5068 undef) (bit_and (notBool_ v_5068) (bit_or (bit_and v_5041 (isBitSet v_5046 0)) (bit_and v_5040 (eq v_5073 (expression.bv_nat 1 1))))));
      v_5083 <- eval (bit_and v_5041 undef);
      v_5084 <- getRegister of;
      v_5090 <- getRegister af;
      setRegister (lhs.of_reg v_2871) v_5047;
      setRegister af (bit_or v_5083 (bit_and v_5040 (eq v_5090 (expression.bv_nat 1 1))));
      setRegister cf v_5078;
      setRegister of (bit_or (bit_and v_5067 (notBool_ (eq v_5078 v_5054))) (bit_and (notBool_ v_5067) (bit_or v_5083 (bit_and v_5040 (eq v_5084 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5041 (parityFlag (extract v_5046 9 17))) (bit_and v_5040 (eq v_5063 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5041 v_5054) (bit_and v_5040 (eq v_5056 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5041 (eq v_5047 (expression.bv_nat 16 0))) (bit_and v_5040 (eq v_5050 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun cl (v_2855 : Mem) => do
      v_9935 <- evaluateAddress v_2855;
      v_9936 <- load v_9935 2;
      v_9938 <- getRegister rcx;
      v_9940 <- eval (bv_and (extract v_9938 56 64) (expression.bv_nat 8 31));
      v_9943 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9936) (concat (expression.bv_nat 9 0) v_9940)) 0 17);
      v_9944 <- eval (extract v_9943 1 17);
      store v_9935 v_9944 2;
      v_9946 <- eval (eq v_9940 (expression.bv_nat 8 0));
      v_9947 <- eval (notBool_ v_9946);
      v_9950 <- getRegister zf;
      v_9954 <- eval (isBitSet v_9943 1);
      v_9956 <- getRegister sf;
      v_9963 <- getRegister pf;
      v_9967 <- eval (eq v_9940 (expression.bv_nat 8 1));
      v_9968 <- eval (uge v_9940 (expression.bv_nat 8 16));
      v_9973 <- getRegister cf;
      v_9978 <- eval (bit_or (bit_and v_9968 undef) (bit_and (notBool_ v_9968) (bit_or (bit_and v_9947 (isBitSet v_9943 0)) (bit_and v_9946 (eq v_9973 (expression.bv_nat 1 1))))));
      v_9983 <- eval (bit_and v_9947 undef);
      v_9984 <- getRegister of;
      v_9990 <- getRegister af;
      setRegister af (bit_or v_9983 (bit_and v_9946 (eq v_9990 (expression.bv_nat 1 1))));
      setRegister cf v_9978;
      setRegister of (bit_or (bit_and v_9967 (notBool_ (eq v_9978 v_9954))) (bit_and (notBool_ v_9967) (bit_or v_9983 (bit_and v_9946 (eq v_9984 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_9947 (parityFlag (extract v_9943 9 17))) (bit_and v_9946 (eq v_9963 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_9947 v_9954) (bit_and v_9946 (eq v_9956 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_9947 (eq v_9944 (expression.bv_nat 16 0))) (bit_and v_9946 (eq v_9950 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2859 : imm int) (v_2858 : Mem) => do
      v_10000 <- evaluateAddress v_2858;
      v_10001 <- load v_10000 2;
      v_10004 <- eval (bv_and (handleImmediateWithSignExtend v_2859 8 8) (expression.bv_nat 8 31));
      v_10007 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_10001) (concat (expression.bv_nat 9 0) v_10004)) 0 17);
      v_10008 <- eval (extract v_10007 1 17);
      store v_10000 v_10008 2;
      v_10010 <- eval (eq v_10004 (expression.bv_nat 8 0));
      v_10011 <- eval (notBool_ v_10010);
      v_10014 <- getRegister zf;
      v_10018 <- eval (isBitSet v_10007 1);
      v_10020 <- getRegister sf;
      v_10027 <- getRegister pf;
      v_10031 <- eval (eq v_10004 (expression.bv_nat 8 1));
      v_10032 <- eval (uge v_10004 (expression.bv_nat 8 16));
      v_10037 <- getRegister cf;
      v_10042 <- eval (bit_or (bit_and v_10032 undef) (bit_and (notBool_ v_10032) (bit_or (bit_and v_10011 (isBitSet v_10007 0)) (bit_and v_10010 (eq v_10037 (expression.bv_nat 1 1))))));
      v_10047 <- eval (bit_and v_10011 undef);
      v_10048 <- getRegister of;
      v_10054 <- getRegister af;
      setRegister af (bit_or v_10047 (bit_and v_10010 (eq v_10054 (expression.bv_nat 1 1))));
      setRegister cf v_10042;
      setRegister of (bit_or (bit_and v_10031 (notBool_ (eq v_10042 v_10018))) (bit_and (notBool_ v_10031) (bit_or v_10047 (bit_and v_10010 (eq v_10048 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_10011 (parityFlag (extract v_10007 9 17))) (bit_and v_10010 (eq v_10027 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_10011 v_10018) (bit_and v_10010 (eq v_10020 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_10011 (eq v_10008 (expression.bv_nat 16 0))) (bit_and v_10010 (eq v_10014 (expression.bv_nat 1 1))));
      pure ()
    pat_end
