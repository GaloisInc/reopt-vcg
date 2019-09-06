def shrw1 : instruction :=
  definst "shrw" $ do
    pattern fun (_ : clReg) (v_3064 : reg (bv 16)) => do
      v_5285 <- getRegister rcx;
      v_5287 <- eval (bv_and (extract v_5285 56 64) (expression.bv_nat 8 31));
      v_5288 <- eval (eq v_5287 (expression.bv_nat 8 0));
      v_5289 <- getRegister zf;
      v_5290 <- getRegister v_3064;
      v_5293 <- eval (lshr (concat v_5290 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_5287));
      v_5294 <- eval (extract v_5293 0 16);
      v_5297 <- getRegister sf;
      v_5300 <- getRegister pf;
      v_5306 <- getRegister of;
      v_5310 <- getRegister cf;
      v_5314 <- getRegister af;
      setRegister (lhs.of_reg v_3064) v_5294;
      setRegister af (mux v_5288 v_5314 undef);
      setRegister cf (mux (uge v_5287 (expression.bv_nat 8 16)) undef (mux v_5288 v_5310 (isBitSet v_5293 16)));
      setRegister of (mux (eq v_5287 (expression.bv_nat 8 1)) (isBitSet v_5290 0) (mux v_5288 v_5306 undef));
      setRegister pf (mux v_5288 v_5300 (parityFlag (extract v_5293 8 16)));
      setRegister sf (mux v_5288 v_5297 (isBitSet v_5293 0));
      setRegister zf (mux v_5288 v_5289 (eq v_5294 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3068 : imm int) (v_3069 : reg (bv 16)) => do
      v_5324 <- eval (bv_and (handleImmediateWithSignExtend v_3068 8 8) (expression.bv_nat 8 31));
      v_5325 <- eval (eq v_5324 (expression.bv_nat 8 0));
      v_5326 <- getRegister zf;
      v_5327 <- getRegister v_3069;
      v_5330 <- eval (lshr (concat v_5327 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_5324));
      v_5331 <- eval (extract v_5330 0 16);
      v_5334 <- getRegister sf;
      v_5337 <- getRegister pf;
      v_5343 <- getRegister of;
      v_5347 <- getRegister cf;
      v_5351 <- getRegister af;
      setRegister (lhs.of_reg v_3069) v_5331;
      setRegister af (mux v_5325 v_5351 undef);
      setRegister cf (mux (uge v_5324 (expression.bv_nat 8 16)) undef (mux v_5325 v_5347 (isBitSet v_5330 16)));
      setRegister of (mux (eq v_5324 (expression.bv_nat 8 1)) (isBitSet v_5327 0) (mux v_5325 v_5343 undef));
      setRegister pf (mux v_5325 v_5337 (parityFlag (extract v_5330 8 16)));
      setRegister sf (mux v_5325 v_5334 (isBitSet v_5330 0));
      setRegister zf (mux v_5325 v_5326 (eq v_5331 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3073 : reg (bv 16)) => do
      v_6626 <- getRegister v_3073;
      v_6628 <- eval (lshr (concat v_6626 (expression.bv_nat 1 0)) (expression.bv_nat 17 1));
      v_6629 <- eval (extract v_6628 0 16);
      setRegister (lhs.of_reg v_3073) v_6629;
      setRegister af undef;
      setRegister cf (isBitSet v_6628 16);
      setRegister of (isBitSet v_6626 0);
      setRegister pf (parityFlag (extract v_6628 8 16));
      setRegister sf (isBitSet v_6628 0);
      setRegister zf (zeroFlag v_6629);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3051 : Mem) => do
      v_9652 <- evaluateAddress v_3051;
      v_9653 <- load v_9652 2;
      v_9655 <- getRegister rcx;
      v_9657 <- eval (bv_and (extract v_9655 56 64) (expression.bv_nat 8 31));
      v_9659 <- eval (lshr (concat v_9653 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_9657));
      v_9660 <- eval (extract v_9659 0 16);
      store v_9652 v_9660 2;
      v_9662 <- eval (eq v_9657 (expression.bv_nat 8 0));
      v_9663 <- getRegister zf;
      v_9666 <- getRegister sf;
      v_9669 <- getRegister pf;
      v_9675 <- getRegister of;
      v_9679 <- getRegister cf;
      v_9683 <- getRegister af;
      setRegister af (mux v_9662 v_9683 undef);
      setRegister cf (mux (uge v_9657 (expression.bv_nat 8 16)) undef (mux v_9662 v_9679 (isBitSet v_9659 16)));
      setRegister of (mux (eq v_9657 (expression.bv_nat 8 1)) (isBitSet v_9653 0) (mux v_9662 v_9675 undef));
      setRegister pf (mux v_9662 v_9669 (parityFlag (extract v_9659 8 16)));
      setRegister sf (mux v_9662 v_9666 (isBitSet v_9659 0));
      setRegister zf (mux v_9662 v_9663 (eq v_9660 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3055 : imm int) (v_3054 : Mem) => do
      v_9691 <- evaluateAddress v_3054;
      v_9692 <- load v_9691 2;
      v_9695 <- eval (bv_and (handleImmediateWithSignExtend v_3055 8 8) (expression.bv_nat 8 31));
      v_9697 <- eval (lshr (concat v_9692 (expression.bv_nat 1 0)) (concat (expression.bv_nat 9 0) v_9695));
      v_9698 <- eval (extract v_9697 0 16);
      store v_9691 v_9698 2;
      v_9700 <- eval (eq v_9695 (expression.bv_nat 8 0));
      v_9701 <- getRegister zf;
      v_9704 <- getRegister sf;
      v_9707 <- getRegister pf;
      v_9713 <- getRegister of;
      v_9717 <- getRegister cf;
      v_9721 <- getRegister af;
      setRegister af (mux v_9700 v_9721 undef);
      setRegister cf (mux (uge v_9695 (expression.bv_nat 8 16)) undef (mux v_9700 v_9717 (isBitSet v_9697 16)));
      setRegister of (mux (eq v_9695 (expression.bv_nat 8 1)) (isBitSet v_9692 0) (mux v_9700 v_9713 undef));
      setRegister pf (mux v_9700 v_9707 (parityFlag (extract v_9697 8 16)));
      setRegister sf (mux v_9700 v_9704 (isBitSet v_9697 0));
      setRegister zf (mux v_9700 v_9701 (eq v_9698 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3058 : Mem) => do
      v_10141 <- evaluateAddress v_3058;
      v_10142 <- load v_10141 2;
      v_10144 <- eval (lshr (concat v_10142 (expression.bv_nat 1 0)) (expression.bv_nat 17 1));
      v_10145 <- eval (extract v_10144 0 16);
      store v_10141 v_10145 2;
      setRegister af undef;
      setRegister cf (isBitSet v_10144 16);
      setRegister of (isBitSet v_10142 0);
      setRegister pf (parityFlag (extract v_10144 8 16));
      setRegister sf (isBitSet v_10144 0);
      setRegister zf (zeroFlag v_10145);
      pure ()
    pat_end
