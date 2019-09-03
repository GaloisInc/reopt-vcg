def vpmovzxdq1 : instruction :=
  definst "vpmovzxdq" $ do
    pattern fun (v_2765 : reg (bv 128)) (v_2766 : reg (bv 128)) => do
      v_5831 <- getRegister v_2765;
      setRegister (lhs.of_reg v_2766) (concat (expression.bv_nat 32 0) (concat (extract v_5831 64 96) (concat (expression.bv_nat 32 0) (extract v_5831 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2774 : reg (bv 128)) (v_2776 : reg (bv 256)) => do
      v_5842 <- getRegister v_2774;
      setRegister (lhs.of_reg v_2776) (concat (expression.bv_nat 32 0) (concat (extract v_5842 0 32) (concat (expression.bv_nat 32 0) (concat (extract v_5842 32 64) (concat (expression.bv_nat 32 0) (concat (extract v_5842 64 96) (concat (expression.bv_nat 32 0) (extract v_5842 96 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2760 : Mem) (v_2761 : reg (bv 128)) => do
      v_12464 <- evaluateAddress v_2760;
      v_12465 <- load v_12464 8;
      setRegister (lhs.of_reg v_2761) (concat (expression.bv_nat 32 0) (concat (extract v_12465 0 32) (concat (expression.bv_nat 32 0) (extract v_12465 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2769 : Mem) (v_2771 : reg (bv 256)) => do
      v_12472 <- evaluateAddress v_2769;
      v_12473 <- load v_12472 16;
      setRegister (lhs.of_reg v_2771) (concat (expression.bv_nat 32 0) (concat (extract v_12473 0 32) (concat (expression.bv_nat 32 0) (concat (extract v_12473 32 64) (concat (expression.bv_nat 32 0) (concat (extract v_12473 64 96) (concat (expression.bv_nat 32 0) (extract v_12473 96 128))))))));
      pure ()
    pat_end
