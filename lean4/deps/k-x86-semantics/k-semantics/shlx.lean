def shlx1 : instruction :=
  definst "shlx" $ do
    pattern fun (v_2837 : reg (bv 32)) (v_2838 : reg (bv 32)) (v_2839 : reg (bv 32)) => do
      v_7842 <- getRegister v_2838;
      v_7843 <- getRegister v_2837;
      setRegister (lhs.of_reg v_2839) (extract (shl v_7842 (uvalueMInt (bv_and v_7843 (expression.bv_nat 32 31)))) 0 32);
      pure ()
    pat_end;
    pattern fun (v_2858 : reg (bv 64)) (v_2859 : reg (bv 64)) (v_2860 : reg (bv 64)) => do
      v_7860 <- getRegister v_2859;
      v_7861 <- getRegister v_2858;
      setRegister (lhs.of_reg v_2860) (extract (shl v_7860 (uvalueMInt (bv_and v_7861 (expression.bv_nat 64 63)))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_2827 : reg (bv 32)) (v_2829 : Mem) (v_2828 : reg (bv 32)) => do
      v_11855 <- evaluateAddress v_2829;
      v_11856 <- load v_11855 4;
      v_11857 <- getRegister v_2827;
      setRegister (lhs.of_reg v_2828) (extract (shl v_11856 (uvalueMInt (bv_and v_11857 (expression.bv_nat 32 31)))) 0 32);
      pure ()
    pat_end;
    pattern fun (v_2848 : reg (bv 64)) (v_2850 : Mem) (v_2849 : reg (bv 64)) => do
      v_11863 <- evaluateAddress v_2850;
      v_11864 <- load v_11863 8;
      v_11865 <- getRegister v_2848;
      setRegister (lhs.of_reg v_2849) (extract (shl v_11864 (uvalueMInt (bv_and v_11865 (expression.bv_nat 64 63)))) 0 64);
      pure ()
    pat_end
