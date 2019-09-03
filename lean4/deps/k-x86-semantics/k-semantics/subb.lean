def subb1 : instruction :=
  definst "subb" $ do
    pattern fun (v_3094 : imm int) al => do
      v_6776 <- eval (handleImmediateWithSignExtend v_3094 8 8);
      v_6782 <- getRegister rax;
      v_6785 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6776 (mi (bitwidthMInt v_6776) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) (extract v_6782 56 64)));
      v_6790 <- eval (extract v_6785 1 2);
      v_6796 <- eval (extract v_6785 1 9);
      v_6799 <- eval (extract v_6776 0 1);
      v_6803 <- eval (eq (bv_xor v_6799 (mi (bitwidthMInt v_6799) -1)) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_6782 0 56) v_6796);
      setRegister of (mux (bit_and (eq v_6803 (eq (extract v_6782 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_6803 (eq v_6790 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_6796);
      setRegister zf (zeroFlag v_6796);
      setRegister af (bv_xor (bv_xor (extract v_6776 3 4) (extract v_6782 59 60)) (extract v_6785 4 5));
      setRegister sf v_6790;
      setRegister cf (mux (notBool_ (eq (extract v_6785 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3110 : imm int) (v_3112 : reg (bv 8)) => do
      v_6833 <- eval (handleImmediateWithSignExtend v_3110 8 8);
      v_6839 <- getRegister v_3112;
      v_6841 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6833 (mi (bitwidthMInt v_6833) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_6839));
      v_6846 <- eval (extract v_6841 1 2);
      v_6847 <- eval (extract v_6841 1 9);
      v_6854 <- eval (extract v_6833 0 1);
      v_6858 <- eval (eq (bv_xor v_6854 (mi (bitwidthMInt v_6854) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3112) v_6847;
      setRegister of (mux (bit_and (eq v_6858 (eq (extract v_6839 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_6858 (eq v_6846 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_6847);
      setRegister af (bv_xor (extract (bv_xor v_6833 v_6839) 3 4) (extract v_6841 4 5));
      setRegister zf (zeroFlag v_6847);
      setRegister sf v_6846;
      setRegister cf (mux (notBool_ (eq (extract v_6841 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3120 : reg (bv 8)) (v_3121 : reg (bv 8)) => do
      v_6878 <- getRegister v_3120;
      v_6884 <- getRegister v_3121;
      v_6886 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6878 (mi (bitwidthMInt v_6878) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_6884));
      v_6891 <- eval (extract v_6886 1 2);
      v_6892 <- eval (extract v_6886 1 9);
      v_6899 <- eval (extract v_6878 0 1);
      v_6903 <- eval (eq (bv_xor v_6899 (mi (bitwidthMInt v_6899) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3121) v_6892;
      setRegister of (mux (bit_and (eq v_6903 (eq (extract v_6884 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_6903 (eq v_6891 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_6892);
      setRegister af (bv_xor (extract (bv_xor v_6878 v_6884) 3 4) (extract v_6886 4 5));
      setRegister zf (zeroFlag v_6892);
      setRegister sf v_6891;
      setRegister cf (mux (notBool_ (eq (extract v_6886 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3115 : Mem) (v_3116 : reg (bv 8)) => do
      v_10288 <- evaluateAddress v_3115;
      v_10289 <- load v_10288 1;
      v_10295 <- getRegister v_3116;
      v_10297 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10289 (mi (bitwidthMInt v_10289) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_10295));
      v_10302 <- eval (extract v_10297 1 2);
      v_10307 <- eval (extract v_10297 1 9);
      v_10310 <- eval (extract v_10289 0 1);
      v_10314 <- eval (eq (bv_xor v_10310 (mi (bitwidthMInt v_10310) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3116) v_10307;
      setRegister of (mux (bit_and (eq v_10314 (eq (extract v_10295 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10314 (eq v_10302 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10307);
      setRegister zf (zeroFlag v_10307);
      setRegister af (bv_xor (extract (bv_xor v_10289 v_10295) 3 4) (extract v_10297 4 5));
      setRegister sf v_10302;
      setRegister cf (mux (notBool_ (eq (extract v_10297 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3134 : Mem) (v_3135 : reg (bv 8)) => do
      v_10330 <- evaluateAddress v_3134;
      v_10331 <- load v_10330 1;
      v_10337 <- getRegister v_3135;
      v_10339 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10331 (mi (bitwidthMInt v_10331) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_10337));
      v_10344 <- eval (extract v_10339 1 2);
      v_10345 <- eval (extract v_10339 1 9);
      v_10352 <- eval (extract v_10331 0 1);
      v_10356 <- eval (eq (bv_xor v_10352 (mi (bitwidthMInt v_10352) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3135) v_10345;
      setRegister of (mux (bit_and (eq v_10356 (eq (extract v_10337 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10356 (eq v_10344 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10345);
      setRegister af (bv_xor (extract (bv_xor v_10331 v_10337) 3 4) (extract v_10339 4 5));
      setRegister zf (zeroFlag v_10345);
      setRegister sf v_10344;
      setRegister cf (mux (notBool_ (eq (extract v_10339 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3098 : imm int) (v_3099 : Mem) => do
      v_12949 <- evaluateAddress v_3099;
      v_12950 <- eval (handleImmediateWithSignExtend v_3098 8 8);
      v_12956 <- load v_12949 1;
      v_12958 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_12950 (mi (bitwidthMInt v_12950) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_12956));
      v_12959 <- eval (extract v_12958 1 9);
      store v_12949 v_12959 1;
      v_12965 <- eval (extract v_12958 1 2);
      v_12972 <- eval (extract v_12950 0 1);
      v_12976 <- eval (eq (bv_xor v_12972 (mi (bitwidthMInt v_12972) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_12976 (eq (extract v_12956 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_12976 (eq v_12965 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_12959);
      setRegister af (bv_xor (extract (bv_xor v_12950 v_12956) 3 4) (extract v_12958 4 5));
      setRegister zf (zeroFlag v_12959);
      setRegister sf v_12965;
      setRegister cf (mux (notBool_ (eq (extract v_12958 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3103 : reg (bv 8)) (v_3102 : Mem) => do
      v_12991 <- evaluateAddress v_3102;
      v_12992 <- getRegister v_3103;
      v_12998 <- load v_12991 1;
      v_13000 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_12992 (mi (bitwidthMInt v_12992) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_12998));
      v_13001 <- eval (extract v_13000 1 9);
      store v_12991 v_13001 1;
      v_13007 <- eval (extract v_13000 1 2);
      v_13014 <- eval (extract v_12992 0 1);
      v_13018 <- eval (eq (bv_xor v_13014 (mi (bitwidthMInt v_13014) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13018 (eq (extract v_12998 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13018 (eq v_13007 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_13001);
      setRegister af (bv_xor (extract (bv_xor v_12992 v_12998) 3 4) (extract v_13000 4 5));
      setRegister zf (zeroFlag v_13001);
      setRegister sf v_13007;
      setRegister cf (mux (notBool_ (eq (extract v_13000 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
