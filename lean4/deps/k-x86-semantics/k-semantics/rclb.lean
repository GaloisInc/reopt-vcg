def rclb1 : instruction :=
  definst "rclb" $ do
    pattern fun cl (v_3335 : reg (bv 8)) => do
      v_8928 <- getRegister rcx;
      v_8932 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_8928 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_8933 <- eval (extract v_8932 1 9);
      v_8934 <- eval (eq v_8933 (expression.bv_nat 8 1));
      v_8935 <- getRegister cf;
      v_8938 <- getRegister v_3335;
      v_8940 <- eval (rol (concat (mux (eq v_8935 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_8938) v_8932);
      v_8941 <- eval (isBitSet v_8940 0);
      v_8947 <- eval (eq v_8933 (expression.bv_nat 8 0));
      v_8950 <- getRegister of;
      setRegister (lhs.of_reg v_3335) (extract v_8940 1 9);
      setRegister cf v_8941;
      setRegister of (bit_or (bit_and v_8934 (notBool_ (eq v_8941 (isBitSet v_8940 1)))) (bit_and (notBool_ v_8934) (bit_or (bit_and (notBool_ v_8947) undef) (bit_and v_8947 (eq v_8950 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_3339 : imm int) (v_3340 : reg (bv 8)) => do
      v_8963 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_3339 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_8964 <- eval (extract v_8963 1 9);
      v_8965 <- eval (eq v_8964 (expression.bv_nat 8 1));
      v_8966 <- getRegister cf;
      v_8969 <- getRegister v_3340;
      v_8971 <- eval (rol (concat (mux (eq v_8966 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_8969) v_8963);
      v_8972 <- eval (isBitSet v_8971 0);
      v_8978 <- eval (eq v_8964 (expression.bv_nat 8 0));
      v_8981 <- getRegister of;
      setRegister (lhs.of_reg v_3340) (extract v_8971 1 9);
      setRegister cf v_8972;
      setRegister of (bit_or (bit_and v_8965 (notBool_ (eq v_8972 (isBitSet v_8971 1)))) (bit_and (notBool_ v_8965) (bit_or (bit_and (notBool_ v_8978) undef) (bit_and v_8978 (eq v_8981 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_3312 : Mem) => do
      v_15296 <- evaluateAddress v_3312;
      v_15297 <- getRegister cf;
      v_15300 <- load v_15296 1;
      v_15302 <- getRegister rcx;
      v_15306 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_15302 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_15307 <- eval (rol (concat (mux (eq v_15297 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15300) v_15306);
      store v_15296 (extract v_15307 1 9) 1;
      v_15310 <- eval (extract v_15306 1 9);
      v_15311 <- eval (eq v_15310 (expression.bv_nat 8 1));
      v_15312 <- eval (isBitSet v_15307 0);
      v_15318 <- eval (eq v_15310 (expression.bv_nat 8 0));
      v_15321 <- getRegister of;
      setRegister cf v_15312;
      setRegister of (bit_or (bit_and v_15311 (notBool_ (eq v_15312 (isBitSet v_15307 1)))) (bit_and (notBool_ v_15311) (bit_or (bit_and (notBool_ v_15318) undef) (bit_and v_15318 (eq v_15321 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_3315 : imm int) (v_3316 : Mem) => do
      v_15329 <- evaluateAddress v_3316;
      v_15330 <- getRegister cf;
      v_15333 <- load v_15329 1;
      v_15338 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_3315 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_15339 <- eval (rol (concat (mux (eq v_15330 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_15333) v_15338);
      store v_15329 (extract v_15339 1 9) 1;
      v_15342 <- eval (extract v_15338 1 9);
      v_15343 <- eval (eq v_15342 (expression.bv_nat 8 1));
      v_15344 <- eval (isBitSet v_15339 0);
      v_15350 <- eval (eq v_15342 (expression.bv_nat 8 0));
      v_15353 <- getRegister of;
      setRegister cf v_15344;
      setRegister of (bit_or (bit_and v_15343 (notBool_ (eq v_15344 (isBitSet v_15339 1)))) (bit_and (notBool_ v_15343) (bit_or (bit_and (notBool_ v_15350) undef) (bit_and v_15350 (eq v_15353 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
