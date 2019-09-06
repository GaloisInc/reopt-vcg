def salw1 : instruction :=
  definst "salw" $ do
    pattern fun (_ : clReg) (v_3073 : reg (bv 16)) => do
      v_5763 <- getRegister rcx;
      v_5765 <- eval (bv_and (extract v_5763 56 64) (expression.bv_nat 8 31));
      v_5766 <- eval (eq v_5765 (expression.bv_nat 8 0));
      v_5767 <- getRegister zf;
      v_5768 <- getRegister v_3073;
      v_5772 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5768) (concat (expression.bv_nat 9 0) v_5765)) 0 17);
      v_5773 <- eval (extract v_5772 1 17);
      v_5776 <- getRegister sf;
      v_5777 <- eval (isBitSet v_5772 1);
      v_5779 <- getRegister pf;
      v_5785 <- getRegister cf;
      v_5788 <- eval (mux (uge v_5765 (expression.bv_nat 8 16)) undef (mux v_5766 v_5785 (isBitSet v_5772 0)));
      v_5791 <- getRegister of;
      v_5794 <- getRegister af;
      setRegister (lhs.of_reg v_3073) v_5773;
      setRegister af (mux v_5766 v_5794 undef);
      setRegister cf v_5788;
      setRegister of (mux (eq v_5765 (expression.bv_nat 8 1)) (notBool_ (eq v_5788 v_5777)) (mux v_5766 v_5791 undef));
      setRegister pf (mux v_5766 v_5779 (parityFlag (extract v_5772 9 17)));
      setRegister sf (mux v_5766 v_5776 v_5777);
      setRegister zf (mux v_5766 v_5767 (eq v_5773 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3075 : imm int) (v_3078 : reg (bv 16)) => do
      v_5804 <- eval (bv_and (handleImmediateWithSignExtend v_3075 8 8) (expression.bv_nat 8 31));
      v_5805 <- eval (eq v_5804 (expression.bv_nat 8 0));
      v_5806 <- getRegister zf;
      v_5807 <- getRegister v_3078;
      v_5811 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5807) (concat (expression.bv_nat 9 0) v_5804)) 0 17);
      v_5812 <- eval (extract v_5811 1 17);
      v_5815 <- getRegister sf;
      v_5816 <- eval (isBitSet v_5811 1);
      v_5818 <- getRegister pf;
      v_5824 <- getRegister cf;
      v_5827 <- eval (mux (uge v_5804 (expression.bv_nat 8 16)) undef (mux v_5805 v_5824 (isBitSet v_5811 0)));
      v_5830 <- getRegister of;
      v_5833 <- getRegister af;
      setRegister (lhs.of_reg v_3078) v_5812;
      setRegister af (mux v_5805 v_5833 undef);
      setRegister cf v_5827;
      setRegister of (mux (eq v_5804 (expression.bv_nat 8 1)) (notBool_ (eq v_5827 v_5816)) (mux v_5805 v_5830 undef));
      setRegister pf (mux v_5805 v_5818 (parityFlag (extract v_5811 9 17)));
      setRegister sf (mux v_5805 v_5815 v_5816);
      setRegister zf (mux v_5805 v_5806 (eq v_5812 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3082 : reg (bv 16)) => do
      v_7617 <- getRegister v_3082;
      v_7620 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_7617) (expression.bv_nat 17 1)) 0 17);
      v_7621 <- eval (extract v_7620 1 17);
      v_7623 <- eval (isBitSet v_7620 1);
      v_7626 <- eval (isBitSet v_7620 0);
      setRegister (lhs.of_reg v_3082) v_7621;
      setRegister af undef;
      setRegister cf v_7626;
      setRegister of (notBool_ (eq v_7626 v_7623));
      setRegister pf (parityFlag (extract v_7620 9 17));
      setRegister sf v_7623;
      setRegister zf (zeroFlag v_7621);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3058 : Mem) => do
      v_12219 <- evaluateAddress v_3058;
      v_12220 <- load v_12219 2;
      v_12222 <- getRegister rcx;
      v_12224 <- eval (bv_and (extract v_12222 56 64) (expression.bv_nat 8 31));
      v_12227 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_12220) (concat (expression.bv_nat 9 0) v_12224)) 0 17);
      v_12228 <- eval (extract v_12227 1 17);
      store v_12219 v_12228 2;
      v_12230 <- eval (eq v_12224 (expression.bv_nat 8 0));
      v_12231 <- getRegister zf;
      v_12234 <- getRegister sf;
      v_12235 <- eval (isBitSet v_12227 1);
      v_12237 <- getRegister pf;
      v_12243 <- getRegister cf;
      v_12246 <- eval (mux (uge v_12224 (expression.bv_nat 8 16)) undef (mux v_12230 v_12243 (isBitSet v_12227 0)));
      v_12249 <- getRegister of;
      v_12252 <- getRegister af;
      setRegister af (mux v_12230 v_12252 undef);
      setRegister cf v_12246;
      setRegister of (mux (eq v_12224 (expression.bv_nat 8 1)) (notBool_ (eq v_12246 v_12235)) (mux v_12230 v_12249 undef));
      setRegister pf (mux v_12230 v_12237 (parityFlag (extract v_12227 9 17)));
      setRegister sf (mux v_12230 v_12234 v_12235);
      setRegister zf (mux v_12230 v_12231 (eq v_12228 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3061 : imm int) (v_3062 : Mem) => do
      v_12260 <- evaluateAddress v_3062;
      v_12261 <- load v_12260 2;
      v_12264 <- eval (bv_and (handleImmediateWithSignExtend v_3061 8 8) (expression.bv_nat 8 31));
      v_12267 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_12261) (concat (expression.bv_nat 9 0) v_12264)) 0 17);
      v_12268 <- eval (extract v_12267 1 17);
      store v_12260 v_12268 2;
      v_12270 <- eval (eq v_12264 (expression.bv_nat 8 0));
      v_12271 <- getRegister zf;
      v_12274 <- getRegister sf;
      v_12275 <- eval (isBitSet v_12267 1);
      v_12277 <- getRegister pf;
      v_12283 <- getRegister cf;
      v_12286 <- eval (mux (uge v_12264 (expression.bv_nat 8 16)) undef (mux v_12270 v_12283 (isBitSet v_12267 0)));
      v_12289 <- getRegister of;
      v_12292 <- getRegister af;
      setRegister af (mux v_12270 v_12292 undef);
      setRegister cf v_12286;
      setRegister of (mux (eq v_12264 (expression.bv_nat 8 1)) (notBool_ (eq v_12286 v_12275)) (mux v_12270 v_12289 undef));
      setRegister pf (mux v_12270 v_12277 (parityFlag (extract v_12267 9 17)));
      setRegister sf (mux v_12270 v_12274 v_12275);
      setRegister zf (mux v_12270 v_12271 (eq v_12268 (expression.bv_nat 16 0)));
      pure ()
    pat_end;
    pattern fun (v_3067 : Mem) => do
      v_13174 <- evaluateAddress v_3067;
      v_13175 <- load v_13174 2;
      v_13178 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13175) (expression.bv_nat 17 1)) 0 17);
      v_13179 <- eval (extract v_13178 1 17);
      store v_13174 v_13179 2;
      v_13182 <- eval (isBitSet v_13178 1);
      v_13185 <- eval (isBitSet v_13178 0);
      setRegister af undef;
      setRegister cf v_13185;
      setRegister of (notBool_ (eq v_13185 v_13182));
      setRegister pf (parityFlag (extract v_13178 9 17));
      setRegister sf v_13182;
      setRegister zf (zeroFlag v_13179);
      pure ()
    pat_end
