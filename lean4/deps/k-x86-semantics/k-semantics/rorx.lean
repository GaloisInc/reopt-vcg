def rorx1 : instruction :=
  definst "rorx" $ do
    pattern fun (v_2836 : imm int) (v_2837 : reg (bv 32)) (v_2838 : reg (bv 32)) => do
      v_8106 <- getRegister v_2837;
      v_8109 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2836 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2838) (bv_or (lshr v_8106 v_8109) (extract (shl v_8106 (sub (expression.bv_nat 32 32) v_8109)) 0 32));
      pure ()
    pat_end;
    pattern fun (v_2857 : imm int) (v_2858 : reg (bv 64)) (v_2859 : reg (bv 64)) => do
      v_8127 <- getRegister v_2858;
      v_8130 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2857 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2859) (bv_or (lshr v_8127 v_8130) (extract (shl v_8127 (sub (expression.bv_nat 64 64) v_8130)) 0 64));
      pure ()
    pat_end;
    pattern fun (v_2826 : imm int) (v_2828 : Mem) (v_2827 : reg (bv 32)) => do
      v_12857 <- evaluateAddress v_2828;
      v_12858 <- load v_12857 4;
      v_12861 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2826 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2827) (bv_or (lshr v_12858 v_12861) (extract (shl v_12858 (sub (expression.bv_nat 32 32) v_12861)) 0 32));
      pure ()
    pat_end;
    pattern fun (v_2847 : imm int) (v_2849 : Mem) (v_2848 : reg (bv 64)) => do
      v_12868 <- evaluateAddress v_2849;
      v_12869 <- load v_12868 8;
      v_12872 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2847 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2848) (bv_or (lshr v_12869 v_12872) (extract (shl v_12869 (sub (expression.bv_nat 64 64) v_12872)) 0 64));
      pure ()
    pat_end
