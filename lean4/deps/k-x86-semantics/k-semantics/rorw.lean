def rorw1 : instruction :=
  definst "rorw" $ do
    pattern fun cl (v_2750 : reg (bv 16)) => do
      v_5617 <- getRegister rcx;
      v_5619 <- eval (bv_and (extract v_5617 56 64) (expression.bv_nat 8 31));
      v_5620 <- eval (eq v_5619 (expression.bv_nat 8 0));
      v_5621 <- eval (notBool_ v_5620);
      v_5622 <- getRegister v_2750;
      v_5625 <- eval (rorHelper v_5622 (uvalueMInt (concat (expression.bv_nat 8 0) v_5619)) 0);
      v_5627 <- eval (eq (extract v_5625 0 1) (expression.bv_nat 1 1));
      v_5629 <- getRegister cf;
      v_5634 <- eval (eq v_5619 (expression.bv_nat 8 1));
      v_5642 <- getRegister of;
      setRegister (lhs.of_reg v_2750) v_5625;
      setRegister of (mux (bit_or (bit_and v_5634 (notBool_ (eq v_5627 (eq (extract v_5625 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5634) (bit_or (bit_and v_5621 undef) (bit_and v_5620 (eq v_5642 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5621 v_5627) (bit_and v_5620 (eq v_5629 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2751 : imm int) (v_2755 : reg (bv 16)) => do
      v_5653 <- eval (bv_and (handleImmediateWithSignExtend v_2751 8 8) (expression.bv_nat 8 31));
      v_5654 <- eval (eq v_5653 (expression.bv_nat 8 0));
      v_5655 <- eval (notBool_ v_5654);
      v_5656 <- getRegister v_2755;
      v_5659 <- eval (rorHelper v_5656 (uvalueMInt (concat (expression.bv_nat 8 0) v_5653)) 0);
      v_5661 <- eval (eq (extract v_5659 0 1) (expression.bv_nat 1 1));
      v_5663 <- getRegister cf;
      v_5668 <- eval (eq v_5653 (expression.bv_nat 8 1));
      v_5676 <- getRegister of;
      setRegister (lhs.of_reg v_2755) v_5659;
      setRegister of (mux (bit_or (bit_and v_5668 (notBool_ (eq v_5661 (eq (extract v_5659 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5668) (bit_or (bit_and v_5655 undef) (bit_and v_5654 (eq v_5676 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5655 v_5661) (bit_and v_5654 (eq v_5663 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2759 : reg (bv 16)) => do
      v_5686 <- getRegister v_2759;
      v_5688 <- eval (bitwidthMInt v_5686);
      v_5689 <- eval (sub v_5688 1);
      v_5693 <- eval (add (lshr v_5686 1) (concat (extract v_5686 v_5689 v_5688) (mi v_5689 0)));
      v_5694 <- eval (extract v_5693 0 1);
      setRegister (lhs.of_reg v_2759) v_5693;
      setRegister of (mux (notBool_ (eq (eq v_5694 (expression.bv_nat 1 1)) (eq (extract v_5693 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5694;
      pure ()
    pat_end;
    pattern fun cl (v_2737 : Mem) => do
      v_15234 <- evaluateAddress v_2737;
      v_15235 <- load v_15234 2;
      v_15236 <- getRegister rcx;
      v_15238 <- eval (bv_and (extract v_15236 56 64) (expression.bv_nat 8 31));
      v_15241 <- eval (rorHelper v_15235 (uvalueMInt (concat (expression.bv_nat 8 0) v_15238)) 0);
      store v_15234 v_15241 2;
      v_15243 <- eval (eq v_15238 (expression.bv_nat 8 0));
      v_15244 <- eval (notBool_ v_15243);
      v_15246 <- eval (eq (extract v_15241 0 1) (expression.bv_nat 1 1));
      v_15248 <- getRegister cf;
      v_15253 <- eval (eq v_15238 (expression.bv_nat 8 1));
      v_15261 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15253 (notBool_ (eq v_15246 (eq (extract v_15241 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15253) (bit_or (bit_and v_15244 undef) (bit_and v_15243 (eq v_15261 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_15244 v_15246) (bit_and v_15243 (eq v_15248 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2740 : imm int) (v_2741 : Mem) => do
      v_15270 <- evaluateAddress v_2741;
      v_15271 <- load v_15270 2;
      v_15273 <- eval (bv_and (handleImmediateWithSignExtend v_2740 8 8) (expression.bv_nat 8 31));
      v_15276 <- eval (rorHelper v_15271 (uvalueMInt (concat (expression.bv_nat 8 0) v_15273)) 0);
      store v_15270 v_15276 2;
      v_15278 <- eval (eq v_15273 (expression.bv_nat 8 0));
      v_15279 <- eval (notBool_ v_15278);
      v_15281 <- eval (eq (extract v_15276 0 1) (expression.bv_nat 1 1));
      v_15283 <- getRegister cf;
      v_15288 <- eval (eq v_15273 (expression.bv_nat 8 1));
      v_15296 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15288 (notBool_ (eq v_15281 (eq (extract v_15276 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15288) (bit_or (bit_and v_15279 undef) (bit_and v_15278 (eq v_15296 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_15279 v_15281) (bit_and v_15278 (eq v_15283 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
