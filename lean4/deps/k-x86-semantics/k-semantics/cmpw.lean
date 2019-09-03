def cmpw1 : instruction :=
  definst "cmpw" $ do
    pattern fun (v_2406 : imm int) ax => do
      v_3873 <- eval (handleImmediateWithSignExtend v_2406 16 16);
      v_3879 <- getRegister rax;
      v_3882 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3873 (mi (bitwidthMInt v_3873) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) (extract v_3879 48 64)));
      v_3887 <- eval (extract v_3882 1 2);
      v_3897 <- eval (extract v_3873 0 1);
      v_3901 <- eval (eq (bv_xor v_3897 (mi (bitwidthMInt v_3897) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3901 (eq (extract v_3879 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_3901 (eq v_3887 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3882 9 17));
      setRegister af (bv_xor (bv_xor (extract v_3873 11 12) (extract v_3879 59 60)) (extract v_3882 12 13));
      setRegister zf (zeroFlag (extract v_3882 1 17));
      setRegister sf v_3887;
      setRegister cf (mux (notBool_ (eq (extract v_3882 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2418 : imm int) (v_2419 : reg (bv 16)) => do
      v_3924 <- eval (handleImmediateWithSignExtend v_2418 16 16);
      v_3930 <- getRegister v_2419;
      v_3932 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3924 (mi (bitwidthMInt v_3924) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_3930));
      v_3937 <- eval (extract v_3932 1 2);
      v_3946 <- eval (extract v_3924 0 1);
      v_3950 <- eval (eq (bv_xor v_3946 (mi (bitwidthMInt v_3946) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3950 (eq (extract v_3930 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3950 (eq v_3937 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3932 9 17));
      setRegister af (bv_xor (extract (bv_xor v_3924 v_3930) 11 12) (extract v_3932 12 13));
      setRegister zf (zeroFlag (extract v_3932 1 17));
      setRegister sf v_3937;
      setRegister cf (mux (notBool_ (eq (extract v_3932 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2427 : reg (bv 16)) (v_2428 : reg (bv 16)) => do
      v_3969 <- getRegister v_2427;
      v_3975 <- getRegister v_2428;
      v_3977 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3969 (mi (bitwidthMInt v_3969) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_3975));
      v_3982 <- eval (extract v_3977 1 2);
      v_3991 <- eval (extract v_3969 0 1);
      v_3995 <- eval (eq (bv_xor v_3991 (mi (bitwidthMInt v_3991) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3995 (eq (extract v_3975 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3995 (eq v_3982 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3977 9 17));
      setRegister af (bv_xor (extract (bv_xor v_3969 v_3975) 11 12) (extract v_3977 12 13));
      setRegister zf (zeroFlag (extract v_3977 1 17));
      setRegister sf v_3982;
      setRegister cf (mux (notBool_ (eq (extract v_3977 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2411 : imm int) (v_2410 : Mem) => do
      v_7853 <- eval (handleImmediateWithSignExtend v_2411 16 16);
      v_7859 <- evaluateAddress v_2410;
      v_7860 <- load v_7859 2;
      v_7862 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7853 (mi (bitwidthMInt v_7853) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7860));
      v_7867 <- eval (extract v_7862 1 2);
      v_7876 <- eval (extract v_7853 0 1);
      v_7880 <- eval (eq (bv_xor v_7876 (mi (bitwidthMInt v_7876) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_7880 (eq (extract v_7860 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7880 (eq v_7867 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7862 9 17));
      setRegister af (bv_xor (extract (bv_xor v_7853 v_7860) 11 12) (extract v_7862 12 13));
      setRegister zf (zeroFlag (extract v_7862 1 17));
      setRegister sf v_7867;
      setRegister cf (mux (notBool_ (eq (extract v_7862 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2415 : reg (bv 16)) (v_2414 : Mem) => do
      v_7895 <- getRegister v_2415;
      v_7901 <- evaluateAddress v_2414;
      v_7902 <- load v_7901 2;
      v_7904 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7895 (mi (bitwidthMInt v_7895) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7902));
      v_7909 <- eval (extract v_7904 1 2);
      v_7918 <- eval (extract v_7895 0 1);
      v_7922 <- eval (eq (bv_xor v_7918 (mi (bitwidthMInt v_7918) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_7922 (eq (extract v_7902 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7922 (eq v_7909 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7904 9 17));
      setRegister af (bv_xor (extract (bv_xor v_7895 v_7902) 11 12) (extract v_7904 12 13));
      setRegister zf (zeroFlag (extract v_7904 1 17));
      setRegister sf v_7909;
      setRegister cf (mux (notBool_ (eq (extract v_7904 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2423 : Mem) (v_2424 : reg (bv 16)) => do
      v_7937 <- evaluateAddress v_2423;
      v_7938 <- load v_7937 2;
      v_7944 <- getRegister v_2424;
      v_7946 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7938 (mi (bitwidthMInt v_7938) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7944));
      v_7951 <- eval (extract v_7946 1 2);
      v_7960 <- eval (extract v_7938 0 1);
      v_7964 <- eval (eq (bv_xor v_7960 (mi (bitwidthMInt v_7960) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_7964 (eq (extract v_7944 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7964 (eq v_7951 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7946 9 17));
      setRegister af (bv_xor (extract (bv_xor v_7938 v_7944) 11 12) (extract v_7946 12 13));
      setRegister zf (zeroFlag (extract v_7946 1 17));
      setRegister sf v_7951;
      setRegister cf (mux (notBool_ (eq (extract v_7946 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
