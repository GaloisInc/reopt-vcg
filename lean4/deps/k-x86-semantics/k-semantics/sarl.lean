def sarl1 : instruction :=
  definst "sarl" $ do
    pattern fun (_ : clReg) (v_3147 : reg (bv 32)) => do
      v_6068 <- getRegister rcx;
      v_6070 <- eval (bv_and (extract v_6068 56 64) (expression.bv_nat 8 31));
      v_6071 <- eval (eq v_6070 (expression.bv_nat 8 0));
      v_6072 <- getRegister zf;
      v_6073 <- getRegister v_3147;
      v_6076 <- eval (ashr (concat v_6073 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_6070));
      v_6077 <- eval (extract v_6076 0 32);
      v_6080 <- getRegister sf;
      v_6083 <- getRegister pf;
      v_6089 <- getRegister of;
      v_6092 <- getRegister cf;
      v_6095 <- getRegister af;
      setRegister (lhs.of_reg v_3147) v_6077;
      setRegister af (mux v_6071 v_6095 undef);
      setRegister cf (mux v_6071 v_6092 (isBitSet v_6076 32));
      setRegister of (bit_and (notBool_ (eq v_6070 (expression.bv_nat 8 1))) (mux v_6071 v_6089 undef));
      setRegister pf (mux v_6071 v_6083 (parityFlag (extract v_6076 24 32)));
      setRegister sf (mux v_6071 v_6080 (isBitSet v_6076 0));
      setRegister zf (mux v_6071 v_6072 (eq v_6077 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3149 : imm int) (v_3152 : reg (bv 32)) => do
      v_6105 <- eval (bv_and (handleImmediateWithSignExtend v_3149 8 8) (expression.bv_nat 8 31));
      v_6106 <- eval (eq v_6105 (expression.bv_nat 8 0));
      v_6107 <- getRegister zf;
      v_6108 <- getRegister v_3152;
      v_6111 <- eval (ashr (concat v_6108 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_6105));
      v_6112 <- eval (extract v_6111 0 32);
      v_6115 <- getRegister sf;
      v_6118 <- getRegister pf;
      v_6124 <- getRegister of;
      v_6127 <- getRegister cf;
      v_6130 <- getRegister af;
      setRegister (lhs.of_reg v_3152) v_6112;
      setRegister af (mux v_6106 v_6130 undef);
      setRegister cf (mux v_6106 v_6127 (isBitSet v_6111 32));
      setRegister of (bit_and (notBool_ (eq v_6105 (expression.bv_nat 8 1))) (mux v_6106 v_6124 undef));
      setRegister pf (mux v_6106 v_6118 (parityFlag (extract v_6111 24 32)));
      setRegister sf (mux v_6106 v_6115 (isBitSet v_6111 0));
      setRegister zf (mux v_6106 v_6107 (eq v_6112 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3156 : reg (bv 32)) => do
      v_7724 <- getRegister v_3156;
      v_7726 <- eval (ashr (concat v_7724 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      v_7727 <- eval (extract v_7726 0 32);
      setRegister (lhs.of_reg v_3156) v_7727;
      setRegister af undef;
      setRegister cf (isBitSet v_7726 32);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_7726 24 32));
      setRegister sf (isBitSet v_7726 0);
      setRegister zf (zeroFlag v_7727);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3132 : Mem) => do
      v_12445 <- evaluateAddress v_3132;
      v_12446 <- load v_12445 4;
      v_12448 <- getRegister rcx;
      v_12450 <- eval (bv_and (extract v_12448 56 64) (expression.bv_nat 8 31));
      v_12452 <- eval (ashr (concat v_12446 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_12450));
      v_12453 <- eval (extract v_12452 0 32);
      store v_12445 v_12453 4;
      v_12455 <- eval (eq v_12450 (expression.bv_nat 8 0));
      v_12456 <- getRegister zf;
      v_12459 <- getRegister sf;
      v_12462 <- getRegister pf;
      v_12468 <- getRegister of;
      v_12471 <- getRegister cf;
      v_12474 <- getRegister af;
      setRegister af (mux v_12455 v_12474 undef);
      setRegister cf (mux v_12455 v_12471 (isBitSet v_12452 32));
      setRegister of (bit_and (notBool_ (eq v_12450 (expression.bv_nat 8 1))) (mux v_12455 v_12468 undef));
      setRegister pf (mux v_12455 v_12462 (parityFlag (extract v_12452 24 32)));
      setRegister sf (mux v_12455 v_12459 (isBitSet v_12452 0));
      setRegister zf (mux v_12455 v_12456 (eq v_12453 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3135 : imm int) (v_3136 : Mem) => do
      v_12482 <- evaluateAddress v_3136;
      v_12483 <- load v_12482 4;
      v_12486 <- eval (bv_and (handleImmediateWithSignExtend v_3135 8 8) (expression.bv_nat 8 31));
      v_12488 <- eval (ashr (concat v_12483 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_12486));
      v_12489 <- eval (extract v_12488 0 32);
      store v_12482 v_12489 4;
      v_12491 <- eval (eq v_12486 (expression.bv_nat 8 0));
      v_12492 <- getRegister zf;
      v_12495 <- getRegister sf;
      v_12498 <- getRegister pf;
      v_12504 <- getRegister of;
      v_12507 <- getRegister cf;
      v_12510 <- getRegister af;
      setRegister af (mux v_12491 v_12510 undef);
      setRegister cf (mux v_12491 v_12507 (isBitSet v_12488 32));
      setRegister of (bit_and (notBool_ (eq v_12486 (expression.bv_nat 8 1))) (mux v_12491 v_12504 undef));
      setRegister pf (mux v_12491 v_12498 (parityFlag (extract v_12488 24 32)));
      setRegister sf (mux v_12491 v_12495 (isBitSet v_12488 0));
      setRegister zf (mux v_12491 v_12492 (eq v_12489 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3141 : Mem) => do
      v_13210 <- evaluateAddress v_3141;
      v_13211 <- load v_13210 4;
      v_13213 <- eval (ashr (concat v_13211 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      v_13214 <- eval (extract v_13213 0 32);
      store v_13210 v_13214 4;
      setRegister af undef;
      setRegister cf (isBitSet v_13213 32);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13213 24 32));
      setRegister sf (isBitSet v_13213 0);
      setRegister zf (zeroFlag v_13214);
      pure ()
    pat_end
