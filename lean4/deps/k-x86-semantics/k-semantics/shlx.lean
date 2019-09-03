def shlx1 : instruction :=
  definst "shlx" $ do
    pattern fun (v_2824 : reg (bv 32)) (v_2825 : reg (bv 32)) (v_2826 : reg (bv 32)) => do
      v_7816 <- getRegister v_2825;
      v_7817 <- getRegister v_2824;
      setRegister (lhs.of_reg v_2826) (extract (shl v_7816 (uvalueMInt (bv_and v_7817 (expression.bv_nat 32 31)))) 0 (bitwidthMInt v_7816));
      pure ()
    pat_end;
    pattern fun (v_2845 : reg (bv 64)) (v_2846 : reg (bv 64)) (v_2847 : reg (bv 64)) => do
      v_7835 <- getRegister v_2846;
      v_7836 <- getRegister v_2845;
      setRegister (lhs.of_reg v_2847) (extract (shl v_7835 (uvalueMInt (bv_and v_7836 (expression.bv_nat 64 63)))) 0 (bitwidthMInt v_7835));
      pure ()
    pat_end;
    pattern fun (v_2815 : reg (bv 32)) (v_2814 : Mem) (v_2816 : reg (bv 32)) => do
      v_11781 <- evaluateAddress v_2814;
      v_11782 <- load v_11781 4;
      v_11783 <- getRegister v_2815;
      setRegister (lhs.of_reg v_2816) (extract (shl v_11782 (uvalueMInt (bv_and v_11783 (expression.bv_nat 32 31)))) 0 (bitwidthMInt v_11782));
      pure ()
    pat_end;
    pattern fun (v_2836 : reg (bv 64)) (v_2835 : Mem) (v_2837 : reg (bv 64)) => do
      v_11790 <- evaluateAddress v_2835;
      v_11791 <- load v_11790 8;
      v_11792 <- getRegister v_2836;
      setRegister (lhs.of_reg v_2837) (extract (shl v_11791 (uvalueMInt (bv_and v_11792 (expression.bv_nat 64 63)))) 0 (bitwidthMInt v_11791));
      pure ()
    pat_end
