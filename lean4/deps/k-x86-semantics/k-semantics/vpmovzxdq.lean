def vpmovzxdq1 : instruction :=
  definst "vpmovzxdq" $ do
    pattern fun (v_2753 : reg (bv 128)) (v_2754 : reg (bv 128)) => do
      v_5884 <- getRegister v_2753;
      setRegister (lhs.of_reg v_2754) (concat (expression.bv_nat 32 0) (concat (extract v_5884 64 96) (concat (expression.bv_nat 32 0) (extract v_5884 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2762 : reg (bv 128)) (v_2763 : reg (bv 256)) => do
      v_5895 <- getRegister v_2762;
      setRegister (lhs.of_reg v_2763) (concat (expression.bv_nat 32 0) (concat (extract v_5895 0 32) (concat (expression.bv_nat 32 0) (concat (extract v_5895 32 64) (concat (expression.bv_nat 32 0) (concat (extract v_5895 64 96) (concat (expression.bv_nat 32 0) (extract v_5895 96 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2750 : Mem) (v_2749 : reg (bv 128)) => do
      v_13008 <- evaluateAddress v_2750;
      v_13009 <- load v_13008 8;
      setRegister (lhs.of_reg v_2749) (concat (expression.bv_nat 32 0) (concat (extract v_13009 0 32) (concat (expression.bv_nat 32 0) (extract v_13009 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2758 : Mem) (v_2759 : reg (bv 256)) => do
      v_13016 <- evaluateAddress v_2758;
      v_13017 <- load v_13016 16;
      setRegister (lhs.of_reg v_2759) (concat (expression.bv_nat 32 0) (concat (extract v_13017 0 32) (concat (expression.bv_nat 32 0) (concat (extract v_13017 32 64) (concat (expression.bv_nat 32 0) (concat (extract v_13017 64 96) (concat (expression.bv_nat 32 0) (extract v_13017 96 128))))))));
      pure ()
    pat_end
