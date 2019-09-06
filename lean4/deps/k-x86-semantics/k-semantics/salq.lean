def salq1 : instruction :=
  definst "salq" $ do
    pattern fun (_ : clReg) (v_3042 : reg (bv 64)) => do
      v_5646 <- getRegister rcx;
      v_5648 <- eval (bv_and (extract v_5646 56 64) (expression.bv_nat 8 63));
      v_5649 <- eval (eq v_5648 (expression.bv_nat 8 0));
      v_5650 <- getRegister zf;
      v_5651 <- getRegister v_3042;
      v_5655 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5651) (concat (expression.bv_nat 57 0) v_5648)) 0 65);
      v_5656 <- eval (extract v_5655 1 65);
      v_5659 <- getRegister sf;
      v_5660 <- eval (isBitSet v_5655 1);
      v_5662 <- getRegister pf;
      v_5668 <- getRegister cf;
      v_5671 <- eval (mux (uge v_5648 (expression.bv_nat 8 64)) undef (mux v_5649 v_5668 (isBitSet v_5655 0)));
      v_5674 <- getRegister of;
      v_5677 <- getRegister af;
      setRegister (lhs.of_reg v_3042) v_5656;
      setRegister af (mux v_5649 v_5677 undef);
      setRegister cf v_5671;
      setRegister of (mux (eq v_5648 (expression.bv_nat 8 1)) (notBool_ (eq v_5671 v_5660)) (mux v_5649 v_5674 undef));
      setRegister pf (mux v_5649 v_5662 (parityFlag (extract v_5655 57 65)));
      setRegister sf (mux v_5649 v_5659 v_5660);
      setRegister zf (mux v_5649 v_5650 (eq v_5656 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3047 : imm int) (v_3046 : reg (bv 64)) => do
      v_5687 <- eval (bv_and (handleImmediateWithSignExtend v_3047 8 8) (expression.bv_nat 8 63));
      v_5688 <- eval (eq v_5687 (expression.bv_nat 8 0));
      v_5689 <- getRegister zf;
      v_5690 <- getRegister v_3046;
      v_5694 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5690) (concat (expression.bv_nat 57 0) v_5687)) 0 65);
      v_5695 <- eval (extract v_5694 1 65);
      v_5698 <- getRegister sf;
      v_5699 <- eval (isBitSet v_5694 1);
      v_5701 <- getRegister pf;
      v_5707 <- getRegister cf;
      v_5710 <- eval (mux (uge v_5687 (expression.bv_nat 8 64)) undef (mux v_5688 v_5707 (isBitSet v_5694 0)));
      v_5713 <- getRegister of;
      v_5716 <- getRegister af;
      setRegister (lhs.of_reg v_3046) v_5695;
      setRegister af (mux v_5688 v_5716 undef);
      setRegister cf v_5710;
      setRegister of (mux (eq v_5687 (expression.bv_nat 8 1)) (notBool_ (eq v_5710 v_5699)) (mux v_5688 v_5713 undef));
      setRegister pf (mux v_5688 v_5701 (parityFlag (extract v_5694 57 65)));
      setRegister sf (mux v_5688 v_5698 v_5699);
      setRegister zf (mux v_5688 v_5689 (eq v_5695 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3051 : reg (bv 64)) => do
      v_7569 <- getRegister v_3051;
      v_7572 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_7569) (expression.bv_nat 65 1)) 0 65);
      v_7573 <- eval (extract v_7572 1 65);
      v_7575 <- eval (isBitSet v_7572 1);
      v_7578 <- eval (isBitSet v_7572 0);
      setRegister (lhs.of_reg v_3051) v_7573;
      setRegister af undef;
      setRegister cf v_7578;
      setRegister of (notBool_ (eq v_7578 v_7575));
      setRegister pf (parityFlag (extract v_7572 57 65));
      setRegister sf v_7575;
      setRegister zf (zeroFlag v_7573);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3029 : Mem) => do
      v_12097 <- evaluateAddress v_3029;
      v_12098 <- load v_12097 8;
      v_12100 <- getRegister rcx;
      v_12102 <- eval (bv_and (extract v_12100 56 64) (expression.bv_nat 8 63));
      v_12105 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_12098) (concat (expression.bv_nat 57 0) v_12102)) 0 65);
      v_12106 <- eval (extract v_12105 1 65);
      store v_12097 v_12106 8;
      v_12108 <- eval (eq v_12102 (expression.bv_nat 8 0));
      v_12109 <- getRegister zf;
      v_12112 <- getRegister sf;
      v_12113 <- eval (isBitSet v_12105 1);
      v_12115 <- getRegister pf;
      v_12121 <- getRegister cf;
      v_12124 <- eval (mux (uge v_12102 (expression.bv_nat 8 64)) undef (mux v_12108 v_12121 (isBitSet v_12105 0)));
      v_12127 <- getRegister of;
      v_12130 <- getRegister af;
      setRegister af (mux v_12108 v_12130 undef);
      setRegister cf v_12124;
      setRegister of (mux (eq v_12102 (expression.bv_nat 8 1)) (notBool_ (eq v_12124 v_12113)) (mux v_12108 v_12127 undef));
      setRegister pf (mux v_12108 v_12115 (parityFlag (extract v_12105 57 65)));
      setRegister sf (mux v_12108 v_12112 v_12113);
      setRegister zf (mux v_12108 v_12109 (eq v_12106 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3032 : imm int) (v_3033 : Mem) => do
      v_12138 <- evaluateAddress v_3033;
      v_12139 <- load v_12138 8;
      v_12142 <- eval (bv_and (handleImmediateWithSignExtend v_3032 8 8) (expression.bv_nat 8 63));
      v_12145 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_12139) (concat (expression.bv_nat 57 0) v_12142)) 0 65);
      v_12146 <- eval (extract v_12145 1 65);
      store v_12138 v_12146 8;
      v_12148 <- eval (eq v_12142 (expression.bv_nat 8 0));
      v_12149 <- getRegister zf;
      v_12152 <- getRegister sf;
      v_12153 <- eval (isBitSet v_12145 1);
      v_12155 <- getRegister pf;
      v_12161 <- getRegister cf;
      v_12164 <- eval (mux (uge v_12142 (expression.bv_nat 8 64)) undef (mux v_12148 v_12161 (isBitSet v_12145 0)));
      v_12167 <- getRegister of;
      v_12170 <- getRegister af;
      setRegister af (mux v_12148 v_12170 undef);
      setRegister cf v_12164;
      setRegister of (mux (eq v_12142 (expression.bv_nat 8 1)) (notBool_ (eq v_12164 v_12153)) (mux v_12148 v_12167 undef));
      setRegister pf (mux v_12148 v_12155 (parityFlag (extract v_12145 57 65)));
      setRegister sf (mux v_12148 v_12152 v_12153);
      setRegister zf (mux v_12148 v_12149 (eq v_12146 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3038 : Mem) => do
      v_13154 <- evaluateAddress v_3038;
      v_13155 <- load v_13154 8;
      v_13158 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13155) (expression.bv_nat 65 1)) 0 65);
      v_13159 <- eval (extract v_13158 1 65);
      store v_13154 v_13159 8;
      v_13162 <- eval (isBitSet v_13158 1);
      v_13165 <- eval (isBitSet v_13158 0);
      setRegister af undef;
      setRegister cf v_13165;
      setRegister of (notBool_ (eq v_13165 v_13162));
      setRegister pf (parityFlag (extract v_13158 57 65));
      setRegister sf v_13162;
      setRegister zf (zeroFlag v_13159);
      pure ()
    pat_end
