def sarq1 : instruction :=
  definst "sarq" $ do
    pattern fun (_ : clReg) (v_3174 : reg (bv 64)) => do
      v_6174 <- getRegister rcx;
      v_6176 <- eval (bv_and (extract v_6174 56 64) (expression.bv_nat 8 63));
      v_6177 <- eval (eq v_6176 (expression.bv_nat 8 0));
      v_6178 <- getRegister zf;
      v_6179 <- getRegister v_3174;
      v_6182 <- eval (ashr (concat v_6179 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_6176));
      v_6183 <- eval (extract v_6182 0 64);
      v_6186 <- getRegister sf;
      v_6189 <- getRegister pf;
      v_6195 <- getRegister of;
      v_6198 <- getRegister cf;
      v_6201 <- getRegister af;
      setRegister (lhs.of_reg v_3174) v_6183;
      setRegister af (mux v_6177 v_6201 undef);
      setRegister cf (mux v_6177 v_6198 (isBitSet v_6182 64));
      setRegister of (bit_and (notBool_ (eq v_6176 (expression.bv_nat 8 1))) (mux v_6177 v_6195 undef));
      setRegister pf (mux v_6177 v_6189 (parityFlag (extract v_6182 56 64)));
      setRegister sf (mux v_6177 v_6186 (isBitSet v_6182 0));
      setRegister zf (mux v_6177 v_6178 (eq v_6183 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3179 : imm int) (v_3178 : reg (bv 64)) => do
      v_6211 <- eval (bv_and (handleImmediateWithSignExtend v_3179 8 8) (expression.bv_nat 8 63));
      v_6212 <- eval (eq v_6211 (expression.bv_nat 8 0));
      v_6213 <- getRegister zf;
      v_6214 <- getRegister v_3178;
      v_6217 <- eval (ashr (concat v_6214 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_6211));
      v_6218 <- eval (extract v_6217 0 64);
      v_6221 <- getRegister sf;
      v_6224 <- getRegister pf;
      v_6230 <- getRegister of;
      v_6233 <- getRegister cf;
      v_6236 <- getRegister af;
      setRegister (lhs.of_reg v_3178) v_6218;
      setRegister af (mux v_6212 v_6236 undef);
      setRegister cf (mux v_6212 v_6233 (isBitSet v_6217 64));
      setRegister of (bit_and (notBool_ (eq v_6211 (expression.bv_nat 8 1))) (mux v_6212 v_6230 undef));
      setRegister pf (mux v_6212 v_6224 (parityFlag (extract v_6217 56 64)));
      setRegister sf (mux v_6212 v_6221 (isBitSet v_6217 0));
      setRegister zf (mux v_6212 v_6213 (eq v_6218 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3183 : reg (bv 64)) => do
      v_7769 <- getRegister v_3183;
      v_7771 <- eval (ashr (concat v_7769 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_7772 <- eval (extract v_7771 0 64);
      setRegister (lhs.of_reg v_3183) v_7772;
      setRegister af undef;
      setRegister cf (isBitSet v_7771 64);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_7771 56 64));
      setRegister sf (isBitSet v_7771 0);
      setRegister zf (zeroFlag v_7772);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_3161 : Mem) => do
      v_12553 <- evaluateAddress v_3161;
      v_12554 <- load v_12553 8;
      v_12556 <- getRegister rcx;
      v_12558 <- eval (bv_and (extract v_12556 56 64) (expression.bv_nat 8 63));
      v_12560 <- eval (ashr (concat v_12554 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_12558));
      v_12561 <- eval (extract v_12560 0 64);
      store v_12553 v_12561 8;
      v_12563 <- eval (eq v_12558 (expression.bv_nat 8 0));
      v_12564 <- getRegister zf;
      v_12567 <- getRegister sf;
      v_12570 <- getRegister pf;
      v_12576 <- getRegister of;
      v_12579 <- getRegister cf;
      v_12582 <- getRegister af;
      setRegister af (mux v_12563 v_12582 undef);
      setRegister cf (mux v_12563 v_12579 (isBitSet v_12560 64));
      setRegister of (bit_and (notBool_ (eq v_12558 (expression.bv_nat 8 1))) (mux v_12563 v_12576 undef));
      setRegister pf (mux v_12563 v_12570 (parityFlag (extract v_12560 56 64)));
      setRegister sf (mux v_12563 v_12567 (isBitSet v_12560 0));
      setRegister zf (mux v_12563 v_12564 (eq v_12561 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3164 : imm int) (v_3165 : Mem) => do
      v_12590 <- evaluateAddress v_3165;
      v_12591 <- load v_12590 8;
      v_12594 <- eval (bv_and (handleImmediateWithSignExtend v_3164 8 8) (expression.bv_nat 8 63));
      v_12596 <- eval (ashr (concat v_12591 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) v_12594));
      v_12597 <- eval (extract v_12596 0 64);
      store v_12590 v_12597 8;
      v_12599 <- eval (eq v_12594 (expression.bv_nat 8 0));
      v_12600 <- getRegister zf;
      v_12603 <- getRegister sf;
      v_12606 <- getRegister pf;
      v_12612 <- getRegister of;
      v_12615 <- getRegister cf;
      v_12618 <- getRegister af;
      setRegister af (mux v_12599 v_12618 undef);
      setRegister cf (mux v_12599 v_12615 (isBitSet v_12596 64));
      setRegister of (bit_and (notBool_ (eq v_12594 (expression.bv_nat 8 1))) (mux v_12599 v_12612 undef));
      setRegister pf (mux v_12599 v_12606 (parityFlag (extract v_12596 56 64)));
      setRegister sf (mux v_12599 v_12603 (isBitSet v_12596 0));
      setRegister zf (mux v_12599 v_12600 (eq v_12597 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3170 : Mem) => do
      v_13227 <- evaluateAddress v_3170;
      v_13228 <- load v_13227 8;
      v_13230 <- eval (ashr (concat v_13228 (expression.bv_nat 1 0)) (expression.bv_nat 65 1));
      v_13231 <- eval (extract v_13230 0 64);
      store v_13227 v_13231 8;
      setRegister af undef;
      setRegister cf (isBitSet v_13230 64);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13230 56 64));
      setRegister sf (isBitSet v_13230 0);
      setRegister zf (zeroFlag v_13231);
      pure ()
    pat_end
