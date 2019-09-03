def vpmovzxwd1 : instruction :=
  definst "vpmovzxwd" $ do
    pattern fun (v_2783 : reg (bv 128)) (v_2784 : reg (bv 128)) => do
      v_5859 <- getRegister v_2783;
      setRegister (lhs.of_reg v_2784) (concat (expression.bv_nat 16 0) (concat (extract v_5859 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5859 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5859 96 112) (concat (expression.bv_nat 16 0) (extract v_5859 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2792 : reg (bv 128)) (v_2794 : reg (bv 256)) => do
      v_5876 <- getRegister v_2792;
      setRegister (lhs.of_reg v_2794) (concat (expression.bv_nat 16 0) (concat (extract v_5876 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_5876 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_5876 32 48) (concat (expression.bv_nat 16 0) (concat (extract v_5876 48 64) (concat (expression.bv_nat 16 0) (concat (extract v_5876 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5876 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5876 96 112) (concat (expression.bv_nat 16 0) (extract v_5876 112 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2778 : Mem) (v_2779 : reg (bv 128)) => do
      v_12486 <- evaluateAddress v_2778;
      v_12487 <- load v_12486 8;
      setRegister (lhs.of_reg v_2779) (concat (expression.bv_nat 16 0) (concat (extract v_12487 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12487 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12487 32 48) (concat (expression.bv_nat 16 0) (extract v_12487 48 64))))))));
      pure ()
    pat_end;
    pattern fun (v_2787 : Mem) (v_2789 : reg (bv 256)) => do
      v_12500 <- evaluateAddress v_2787;
      v_12501 <- load v_12500 16;
      setRegister (lhs.of_reg v_2789) (concat (expression.bv_nat 16 0) (concat (extract v_12501 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12501 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12501 32 48) (concat (expression.bv_nat 16 0) (concat (extract v_12501 48 64) (concat (expression.bv_nat 16 0) (concat (extract v_12501 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_12501 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_12501 96 112) (concat (expression.bv_nat 16 0) (extract v_12501 112 128))))))))))))))));
      pure ()
    pat_end
