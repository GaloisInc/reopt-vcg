def sarb1 : instruction :=
  definst "sarb" $ do
    pattern fun (_ : clReg) (v_3119 : reg (bv 8)) => do
      v_5965 <- getRegister rcx;
      v_5967 <- eval (bv_and (extract v_5965 56 64) (expression.bv_nat 8 31));
      v_5968 <- eval (eq v_5967 (expression.bv_nat 8 0));
      v_5969 <- getRegister zf;
      v_5970 <- getRegister v_3119;
      v_5973 <- eval (ashr (concat v_5970 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_5967));
      v_5974 <- eval (extract v_5973 0 8);
      v_5977 <- getRegister sf;
      v_5980 <- getRegister pf;
      v_5985 <- getRegister of;
      v_5988 <- getRegister cf;
      v_5991 <- getRegister af;
      setRegister (lhs.of_reg v_3119) v_5974;
      setRegister af (mux v_5968 v_5991 undef);
      setRegister cf (mux v_5968 v_5988 (isBitSet v_5973 8));
      setRegister of (bit_and (notBool_ (eq v_5967 (expression.bv_nat 8 1))) (mux v_5968 v_5985 undef));
      setRegister pf (mux v_5968 v_5980 (parityFlag v_5974));
      setRegister sf (mux v_5968 v_5977 (isBitSet v_5973 0));
      setRegister zf (mux v_5968 v_5969 (eq v_5974 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_3120 : imm int) (v_3124 : reg (bv 8)) => do
      v_6001 <- eval (bv_and (handleImmediateWithSignExtend v_3120 8 8) (expression.bv_nat 8 31));
      v_6002 <- eval (eq v_6001 (expression.bv_nat 8 0));
      v_6003 <- getRegister zf;
      v_6004 <- getRegister v_3124;
      v_6007 <- eval (ashr (concat v_6004 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_6001));
      v_6008 <- eval (extract v_6007 0 8);
      v_6011 <- getRegister sf;
      v_6014 <- getRegister pf;
      v_6019 <- getRegister of;
      v_6022 <- getRegister cf;
      v_6025 <- getRegister af;
      setRegister (lhs.of_reg v_3124) v_6008;
      setRegister af (mux v_6002 v_6025 undef);
      setRegister cf (mux v_6002 v_6022 (isBitSet v_6007 8));
      setRegister of (bit_and (notBool_ (eq v_6001 (expression.bv_nat 8 1))) (mux v_6002 v_6019 undef));
      setRegister pf (mux v_6002 v_6014 (parityFlag v_6008));
      setRegister sf (mux v_6002 v_6011 (isBitSet v_6007 0));
      setRegister zf (mux v_6002 v_6003 (eq v_6008 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_3127 : reg (bv 8)) => do
      v_7680 <- getRegister v_3127;
      v_7682 <- eval (ashr (concat v_7680 (expression.bv_nat 1 0)) (expression.bv_nat 9 1));
      v_7683 <- eval (extract v_7682 0 8);
      setRegister (lhs.of_reg v_3127) v_7683;
      setRegister af undef;
      setRegister cf (isBitSet v_7682 8);
      setRegister of bit_zero;
      setRegister pf (parityFlag v_7683);
      setRegister sf (isBitSet v_7682 0);
      setRegister zf (zeroFlag v_7683);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3087 : Mem) => do
      v_12341 <- evaluateAddress v_3087;
      v_12342 <- load v_12341 1;
      v_12344 <- getRegister rcx;
      v_12346 <- eval (bv_and (extract v_12344 56 64) (expression.bv_nat 8 31));
      v_12348 <- eval (ashr (concat v_12342 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_12346));
      v_12349 <- eval (extract v_12348 0 8);
      store v_12341 v_12349 1;
      v_12351 <- eval (eq v_12346 (expression.bv_nat 8 0));
      v_12352 <- getRegister zf;
      v_12355 <- getRegister sf;
      v_12358 <- getRegister pf;
      v_12363 <- getRegister of;
      v_12366 <- getRegister cf;
      v_12369 <- getRegister af;
      setRegister af (mux v_12351 v_12369 undef);
      setRegister cf (mux v_12351 v_12366 (isBitSet v_12348 8));
      setRegister of (bit_and (notBool_ (eq v_12346 (expression.bv_nat 8 1))) (mux v_12351 v_12363 undef));
      setRegister pf (mux v_12351 v_12358 (parityFlag v_12349));
      setRegister sf (mux v_12351 v_12355 (isBitSet v_12348 0));
      setRegister zf (mux v_12351 v_12352 (eq v_12349 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_3090 : imm int) (v_3091 : Mem) => do
      v_12377 <- evaluateAddress v_3091;
      v_12378 <- load v_12377 1;
      v_12381 <- eval (bv_and (handleImmediateWithSignExtend v_3090 8 8) (expression.bv_nat 8 31));
      v_12383 <- eval (ashr (concat v_12378 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_12381));
      v_12384 <- eval (extract v_12383 0 8);
      store v_12377 v_12384 1;
      v_12386 <- eval (eq v_12381 (expression.bv_nat 8 0));
      v_12387 <- getRegister zf;
      v_12390 <- getRegister sf;
      v_12393 <- getRegister pf;
      v_12398 <- getRegister of;
      v_12401 <- getRegister cf;
      v_12404 <- getRegister af;
      setRegister af (mux v_12386 v_12404 undef);
      setRegister cf (mux v_12386 v_12401 (isBitSet v_12383 8));
      setRegister of (bit_and (notBool_ (eq v_12381 (expression.bv_nat 8 1))) (mux v_12386 v_12398 undef));
      setRegister pf (mux v_12386 v_12393 (parityFlag v_12384));
      setRegister sf (mux v_12386 v_12390 (isBitSet v_12383 0));
      setRegister zf (mux v_12386 v_12387 (eq v_12384 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_3096 : Mem) => do
      v_13194 <- evaluateAddress v_3096;
      v_13195 <- load v_13194 1;
      v_13197 <- eval (ashr (concat v_13195 (expression.bv_nat 1 0)) (expression.bv_nat 9 1));
      v_13198 <- eval (extract v_13197 0 8);
      store v_13194 v_13198 1;
      setRegister af undef;
      setRegister cf (isBitSet v_13197 8);
      setRegister of bit_zero;
      setRegister pf (parityFlag v_13198);
      setRegister sf (isBitSet v_13197 0);
      setRegister zf (zeroFlag v_13198);
      pure ()
    pat_end
