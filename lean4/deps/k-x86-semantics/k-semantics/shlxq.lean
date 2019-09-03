def shlxq1 : instruction :=
  definst "shlxq" $ do
    pattern fun (v_2851 : reg (bv 64)) (v_2852 : reg (bv 64)) (v_2853 : reg (bv 64)) => do
      v_5470 <- getRegister v_2852;
      v_5471 <- getRegister v_2851;
      setRegister (lhs.of_reg v_2853) (extract (shl v_5470 (uvalueMInt (bv_and v_5471 (expression.bv_nat 64 63)))) 0 (bitwidthMInt v_5470));
      pure ()
    pat_end;
    pattern fun (v_2841 : reg (bv 64)) (v_2840 : Mem) (v_2842 : reg (bv 64)) => do
      v_10088 <- evaluateAddress v_2840;
      v_10089 <- load v_10088 8;
      v_10090 <- getRegister v_2841;
      setRegister (lhs.of_reg v_2842) (extract (shl v_10089 (uvalueMInt (bv_and v_10090 (expression.bv_nat 64 63)))) 0 (bitwidthMInt v_10089));
      pure ()
    pat_end
