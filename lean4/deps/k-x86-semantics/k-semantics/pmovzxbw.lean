def pmovzxbw1 : instruction :=
  definst "pmovzxbw" $ do
    pattern fun (v_2738 : reg (bv 128)) (v_2739 : reg (bv 128)) => do
      v_5614 <- getRegister v_2738;
      setRegister (lhs.of_reg v_2739) (concat (expression.bv_nat 8 0) (concat (extract v_5614 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5614 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5614 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5614 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5614 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5614 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5614 112 120) (concat (expression.bv_nat 8 0) (extract v_5614 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2733 : Mem) (v_2734 : reg (bv 128)) => do
      v_12889 <- evaluateAddress v_2733;
      v_12890 <- load v_12889 8;
      setRegister (lhs.of_reg v_2734) (concat (expression.bv_nat 8 0) (concat (extract v_12890 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12890 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12890 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12890 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12890 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12890 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12890 48 56) (concat (expression.bv_nat 8 0) (extract v_12890 56 64))))))))))))))));
      pure ()
    pat_end
