def btsq1 : instruction :=
  definst "btsq" $ do
    pattern fun (v_3271 : imm int) (v_3274 : reg (bv 64)) => do
      v_6160 <- getRegister v_3274;
      v_6163 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3271 8 8) (expression.bv_nat 8 63)) 64);
      setRegister (lhs.of_reg v_3274) (bv_or v_6160 (extract (shl (expression.bv_nat 64 1) v_6163) 0 64));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6160 v_6163) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3278 : reg (bv 64)) (v_3279 : reg (bv 64)) => do
      v_6175 <- getRegister v_3279;
      v_6176 <- getRegister v_3278;
      v_6177 <- eval (bv_and v_6176 (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_3279) (bv_or v_6175 (extract (shl (expression.bv_nat 64 1) v_6177) 0 64));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6175 v_6177) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3263 : imm int) (v_3266 : Mem) => do
      v_10754 <- evaluateAddress v_3266;
      v_10755 <- eval (handleImmediateWithSignExtend v_3263 8 8);
      v_10759 <- eval (add v_10754 (concat (expression.bv_nat 59 0) (bv_and (extract v_10755 0 5) (expression.bv_nat 5 7))));
      v_10760 <- load v_10759 1;
      v_10763 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10755 5 8) (expression.bv_nat 3 7)));
      store v_10759 (bv_or v_10760 (extract (shl (expression.bv_nat 8 1) v_10763) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10760 v_10763) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3270 : reg (bv 64)) (v_3269 : Mem) => do
      v_10775 <- evaluateAddress v_3269;
      v_10776 <- getRegister v_3270;
      v_10779 <- eval (add v_10775 (concat (expression.bv_nat 3 0) (extract v_10776 0 61)));
      v_10780 <- load v_10779 1;
      v_10782 <- eval (concat (expression.bv_nat 5 0) (extract v_10776 61 64));
      store v_10779 (bv_or v_10780 (extract (shl (expression.bv_nat 8 1) v_10782) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10780 v_10782) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
