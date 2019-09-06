def pmovzxbw1 : instruction :=
  definst "pmovzxbw" $ do
    pattern fun (v_2829 : reg (bv 128)) (v_2830 : reg (bv 128)) => do
      v_5583 <- getRegister v_2829;
      setRegister (lhs.of_reg v_2830) (concat (expression.bv_nat 8 0) (concat (extract v_5583 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5583 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5583 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5583 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5583 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5583 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5583 112 120) (concat (expression.bv_nat 8 0) (extract v_5583 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2825 : Mem) (v_2826 : reg (bv 128)) => do
      v_12308 <- evaluateAddress v_2825;
      v_12309 <- load v_12308 8;
      setRegister (lhs.of_reg v_2826) (concat (expression.bv_nat 8 0) (concat (extract v_12309 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12309 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12309 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12309 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12309 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12309 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12309 48 56) (concat (expression.bv_nat 8 0) (extract v_12309 56 64))))))))))))))));
      pure ()
    pat_end
