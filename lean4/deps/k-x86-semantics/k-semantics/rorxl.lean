def rorxl1 : instruction :=
  definst "rorxl" $ do
    pattern fun (v_2866 : imm int) (v_2869 : reg (bv 32)) (v_2870 : reg (bv 32)) => do
      v_5170 <- getRegister v_2869;
      v_5173 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2866 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2870) (bv_or (lshr v_5170 v_5173) (extract (shl v_5170 (sub (expression.bv_nat 32 32) v_5173)) 0 32));
      pure ()
    pat_end;
    pattern fun (v_2856 : imm int) (v_2857 : Mem) (v_2860 : reg (bv 32)) => do
      v_10492 <- evaluateAddress v_2857;
      v_10493 <- load v_10492 4;
      v_10496 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2856 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2860) (bv_or (lshr v_10493 v_10496) (extract (shl v_10493 (sub (expression.bv_nat 32 32) v_10496)) 0 32));
      pure ()
    pat_end
