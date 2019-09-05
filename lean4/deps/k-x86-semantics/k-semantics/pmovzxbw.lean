def pmovzxbw1 : instruction :=
  definst "pmovzxbw" $ do
    pattern fun (v_2801 : reg (bv 128)) (v_2802 : reg (bv 128)) => do
      v_5556 <- getRegister v_2801;
      setRegister (lhs.of_reg v_2802) (concat (expression.bv_nat 8 0) (concat (extract v_5556 64 72) (concat (expression.bv_nat 8 0) (concat (extract v_5556 72 80) (concat (expression.bv_nat 8 0) (concat (extract v_5556 80 88) (concat (expression.bv_nat 8 0) (concat (extract v_5556 88 96) (concat (expression.bv_nat 8 0) (concat (extract v_5556 96 104) (concat (expression.bv_nat 8 0) (concat (extract v_5556 104 112) (concat (expression.bv_nat 8 0) (concat (extract v_5556 112 120) (concat (expression.bv_nat 8 0) (extract v_5556 120 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2798 : Mem) (v_2797 : reg (bv 128)) => do
      v_12332 <- evaluateAddress v_2798;
      v_12333 <- load v_12332 8;
      setRegister (lhs.of_reg v_2797) (concat (expression.bv_nat 8 0) (concat (extract v_12333 0 8) (concat (expression.bv_nat 8 0) (concat (extract v_12333 8 16) (concat (expression.bv_nat 8 0) (concat (extract v_12333 16 24) (concat (expression.bv_nat 8 0) (concat (extract v_12333 24 32) (concat (expression.bv_nat 8 0) (concat (extract v_12333 32 40) (concat (expression.bv_nat 8 0) (concat (extract v_12333 40 48) (concat (expression.bv_nat 8 0) (concat (extract v_12333 48 56) (concat (expression.bv_nat 8 0) (extract v_12333 56 64))))))))))))))));
      pure ()
    pat_end
