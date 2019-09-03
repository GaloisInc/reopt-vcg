def roll1 : instruction :=
  definst "roll" $ do
    pattern fun cl (v_2598 : reg (bv 32)) => do
      v_4949 <- getRegister rcx;
      v_4951 <- eval (bv_and (extract v_4949 56 64) (expression.bv_nat 8 31));
      v_4952 <- eval (eq v_4951 (expression.bv_nat 8 0));
      v_4953 <- eval (notBool_ v_4952);
      v_4954 <- getRegister v_2598;
      v_4957 <- eval (rolHelper v_4954 (uvalueMInt (concat (expression.bv_nat 24 0) v_4951)) 0);
      v_4959 <- eval (eq (extract v_4957 31 32) (expression.bv_nat 1 1));
      v_4961 <- getRegister cf;
      v_4966 <- eval (eq v_4951 (expression.bv_nat 8 1));
      v_4974 <- getRegister of;
      setRegister (lhs.of_reg v_2598) v_4957;
      setRegister of (mux (bit_or (bit_and v_4966 (notBool_ (eq (eq (extract v_4957 0 1) (expression.bv_nat 1 1)) v_4959))) (bit_and (notBool_ v_4966) (bit_or (bit_and v_4953 undef) (bit_and v_4952 (eq v_4974 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_4953 v_4959) (bit_and v_4952 (eq v_4961 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2600 : imm int) (v_2603 : reg (bv 32)) => do
      v_4985 <- eval (bv_and (handleImmediateWithSignExtend v_2600 8 8) (expression.bv_nat 8 31));
      v_4986 <- eval (eq v_4985 (expression.bv_nat 8 0));
      v_4987 <- eval (notBool_ v_4986);
      v_4988 <- getRegister v_2603;
      v_4991 <- eval (rolHelper v_4988 (uvalueMInt (concat (expression.bv_nat 24 0) v_4985)) 0);
      v_4993 <- eval (eq (extract v_4991 31 32) (expression.bv_nat 1 1));
      v_4995 <- getRegister cf;
      v_5000 <- eval (eq v_4985 (expression.bv_nat 8 1));
      v_5008 <- getRegister of;
      setRegister (lhs.of_reg v_2603) v_4991;
      setRegister of (mux (bit_or (bit_and v_5000 (notBool_ (eq (eq (extract v_4991 0 1) (expression.bv_nat 1 1)) v_4993))) (bit_and (notBool_ v_5000) (bit_or (bit_and v_4987 undef) (bit_and v_4986 (eq v_5008 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_4987 v_4993) (bit_and v_4986 (eq v_4995 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2607 : reg (bv 32)) => do
      v_5018 <- getRegister v_2607;
      v_5020 <- eval (bitwidthMInt v_5018);
      v_5026 <- eval (add (extract (shl v_5018 1) 0 v_5020) (concat (mi (sub v_5020 1) 0) (extract v_5018 0 1)));
      v_5027 <- eval (extract v_5026 31 32);
      setRegister (lhs.of_reg v_2607) v_5026;
      setRegister of (mux (notBool_ (eq (eq (extract v_5026 0 1) (expression.bv_nat 1 1)) (eq v_5027 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5027;
      pure ()
    pat_end;
    pattern fun cl (v_2583 : Mem) => do
      v_14328 <- evaluateAddress v_2583;
      v_14329 <- load v_14328 4;
      v_14330 <- getRegister rcx;
      v_14332 <- eval (bv_and (extract v_14330 56 64) (expression.bv_nat 8 31));
      v_14335 <- eval (rolHelper v_14329 (uvalueMInt (concat (expression.bv_nat 24 0) v_14332)) 0);
      store v_14328 v_14335 4;
      v_14337 <- eval (eq v_14332 (expression.bv_nat 8 0));
      v_14338 <- eval (notBool_ v_14337);
      v_14340 <- eval (eq (extract v_14335 31 32) (expression.bv_nat 1 1));
      v_14342 <- getRegister cf;
      v_14347 <- eval (eq v_14332 (expression.bv_nat 8 1));
      v_14355 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14347 (notBool_ (eq (eq (extract v_14335 0 1) (expression.bv_nat 1 1)) v_14340))) (bit_and (notBool_ v_14347) (bit_or (bit_and v_14338 undef) (bit_and v_14337 (eq v_14355 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14338 v_14340) (bit_and v_14337 (eq v_14342 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2586 : imm int) (v_2587 : Mem) => do
      v_14364 <- evaluateAddress v_2587;
      v_14365 <- load v_14364 4;
      v_14367 <- eval (bv_and (handleImmediateWithSignExtend v_2586 8 8) (expression.bv_nat 8 31));
      v_14370 <- eval (rolHelper v_14365 (uvalueMInt (concat (expression.bv_nat 24 0) v_14367)) 0);
      store v_14364 v_14370 4;
      v_14372 <- eval (eq v_14367 (expression.bv_nat 8 0));
      v_14373 <- eval (notBool_ v_14372);
      v_14375 <- eval (eq (extract v_14370 31 32) (expression.bv_nat 1 1));
      v_14377 <- getRegister cf;
      v_14382 <- eval (eq v_14367 (expression.bv_nat 8 1));
      v_14390 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14382 (notBool_ (eq (eq (extract v_14370 0 1) (expression.bv_nat 1 1)) v_14375))) (bit_and (notBool_ v_14382) (bit_or (bit_and v_14373 undef) (bit_and v_14372 (eq v_14390 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14373 v_14375) (bit_and v_14372 (eq v_14377 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) => do
      v_18157 <- evaluateAddress v_2592;
      v_18158 <- load v_18157 4;
      v_18160 <- eval (bitwidthMInt v_18158);
      v_18166 <- eval (add (extract (shl v_18158 1) 0 v_18160) (concat (mi (sub v_18160 1) 0) (extract v_18158 0 1)));
      store v_18157 v_18166 4;
      v_18169 <- eval (eq (extract v_18166 31 32) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq (eq (extract v_18166 0 1) (expression.bv_nat 1 1)) v_18169)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_18169 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) => do
      v_18178 <- evaluateAddress v_2592;
      v_18179 <- load v_18178 4;
      v_18181 <- eval (bitwidthMInt v_18179);
      v_18187 <- eval (add (extract (shl v_18179 1) 0 v_18181) (concat (mi (sub v_18181 1) 0) (extract v_18179 0 1)));
      store v_18178 v_18187 4;
      v_18189 <- eval (extract v_18187 31 32);
      setRegister of (mux (notBool_ (eq (eq (extract v_18187 0 1) (expression.bv_nat 1 1)) (eq v_18189 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_18189;
      pure ()
    pat_end
