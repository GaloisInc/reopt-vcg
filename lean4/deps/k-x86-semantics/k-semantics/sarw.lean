def sarw1 : instruction :=
  definst "sarw" $ do
    pattern fun (_ : clReg) (v_3205 : reg (bv 16)) => do
      v_6280 <- getRegister rcx;
      v_6282 <- eval (bv_and (extract v_6280 56 64) (expression.bv_nat 8 31));
      v_6283 <- eval (eq v_6282 (expression.bv_nat 8 0));
      v_6284 <- getRegister zf;
      v_6285 <- getRegister v_3205;
      v_6288 <- eval (ashr (concat v_6285 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_6282));
      v_6289 <- eval (extract v_6288 0 16);
      v_6292 <- getRegister sf;
      v_6295 <- getRegister pf;
      v_6301 <- getRegister of;
      v_6304 <- getRegister cf;
      v_6307 <- getRegister af;
      setRegister (lhs.of_reg v_3205) v_6289;
      setRegister af (mux v_6283 v_6307 undef);
      setRegister cf (mux v_6283 v_6304 (isBitSet v_6288 16));
      setRegister of (bit_and (notBool_ (eq v_6282 (expression.bv_nat 8 1))) (mux v_6283 v_6301 undef));
      setRegister pf (mux v_6283 v_6295 (parityFlag (extract v_6288 8 16)));
      setRegister sf (mux v_6283 v_6292 (isBitSet v_6288 0));
      setRegister zf (mux v_6283 v_6284 (eq v_6289 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3207 : imm int) (v_3210 : reg (bv 16)) => do
      v_6317 <- eval (bv_and (handleImmediateWithSignExtend v_3207 8 8) (expression.bv_nat 8 31));
      v_6318 <- eval (eq v_6317 (expression.bv_nat 8 0));
      v_6319 <- getRegister zf;
      v_6320 <- getRegister v_3210;
      v_6323 <- eval (ashr (concat v_6320 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_6317));
      v_6324 <- eval (extract v_6323 0 16);
      v_6327 <- getRegister sf;
      v_6330 <- getRegister pf;
      v_6336 <- getRegister of;
      v_6339 <- getRegister cf;
      v_6342 <- getRegister af;
      setRegister (lhs.of_reg v_3210) v_6324;
      setRegister af (mux v_6318 v_6342 undef);
      setRegister cf (mux v_6318 v_6339 (isBitSet v_6323 16));
      setRegister of (bit_and (notBool_ (eq v_6317 (expression.bv_nat 8 1))) (mux v_6318 v_6336 undef));
      setRegister pf (mux v_6318 v_6330 (parityFlag (extract v_6323 8 16)));
      setRegister sf (mux v_6318 v_6327 (isBitSet v_6323 0));
      setRegister zf (mux v_6318 v_6319 (eq v_6324 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3214 : reg (bv 16)) => do
      v_7814 <- getRegister v_3214;
      v_7816 <- eval (ashr (concat v_7814 (expression.bv_nat 1 0)) (expression.bv_nat 17 1));
      v_7817 <- eval (extract v_7816 0 16);
      setRegister (lhs.of_reg v_3214) v_7817;
      setRegister af undef;
      setRegister cf (isBitSet v_7816 16);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_7816 8 16));
      setRegister sf (isBitSet v_7816 0);
      setRegister zf (zeroFlag v_7817);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3190 : Mem) => do
      v_12661 <- evaluateAddress v_3190;
      v_12662 <- load v_12661 2;
      v_12664 <- getRegister rcx;
      v_12666 <- eval (bv_and (extract v_12664 56 64) (expression.bv_nat 8 31));
      v_12668 <- eval (ashr (concat v_12662 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_12666));
      v_12669 <- eval (extract v_12668 0 16);
      store v_12661 v_12669 2;
      v_12671 <- eval (eq v_12666 (expression.bv_nat 8 0));
      v_12672 <- getRegister zf;
      v_12675 <- getRegister sf;
      v_12678 <- getRegister pf;
      v_12684 <- getRegister of;
      v_12687 <- getRegister cf;
      v_12690 <- getRegister af;
      setRegister af (mux v_12671 v_12690 undef);
      setRegister cf (mux v_12671 v_12687 (isBitSet v_12668 16));
      setRegister of (bit_and (notBool_ (eq v_12666 (expression.bv_nat 8 1))) (mux v_12671 v_12684 undef));
      setRegister pf (mux v_12671 v_12678 (parityFlag (extract v_12668 8 16)));
      setRegister sf (mux v_12671 v_12675 (isBitSet v_12668 0));
      setRegister zf (mux v_12671 v_12672 (eq v_12669 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3193 : imm int) (v_3194 : Mem) => do
      v_12698 <- evaluateAddress v_3194;
      v_12699 <- load v_12698 2;
      v_12702 <- eval (bv_and (handleImmediateWithSignExtend v_3193 8 8) (expression.bv_nat 8 31));
      v_12704 <- eval (ashr (concat v_12699 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_12702));
      v_12705 <- eval (extract v_12704 0 16);
      store v_12698 v_12705 2;
      v_12707 <- eval (eq v_12702 (expression.bv_nat 8 0));
      v_12708 <- getRegister zf;
      v_12711 <- getRegister sf;
      v_12714 <- getRegister pf;
      v_12720 <- getRegister of;
      v_12723 <- getRegister cf;
      v_12726 <- getRegister af;
      setRegister af (mux v_12707 v_12726 undef);
      setRegister cf (mux v_12707 v_12723 (isBitSet v_12704 16));
      setRegister of (bit_and (notBool_ (eq v_12702 (expression.bv_nat 8 1))) (mux v_12707 v_12720 undef));
      setRegister pf (mux v_12707 v_12714 (parityFlag (extract v_12704 8 16)));
      setRegister sf (mux v_12707 v_12711 (isBitSet v_12704 0));
      setRegister zf (mux v_12707 v_12708 (eq v_12705 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3199 : Mem) => do
      v_13244 <- evaluateAddress v_3199;
      v_13245 <- load v_13244 2;
      v_13247 <- eval (ashr (concat v_13245 (expression.bv_nat 1 0)) (expression.bv_nat 17 1));
      v_13248 <- eval (extract v_13247 0 16);
      store v_13244 v_13248 2;
      setRegister af undef;
      setRegister cf (isBitSet v_13247 16);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13247 8 16));
      setRegister sf (isBitSet v_13247 0);
      setRegister zf (zeroFlag v_13248);
      pure ()
    pat_end
