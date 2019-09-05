def pmovzxdq1 : instruction :=
  definst "pmovzxdq" $ do
    pattern fun (v_2810 : reg (bv 128)) (v_2811 : reg (bv 128)) => do
      v_5585 <- getRegister v_2810;
      setRegister (lhs.of_reg v_2811) (concat (expression.bv_nat 32 0) (concat (extract v_5585 64 96) (concat (expression.bv_nat 32 0) (extract v_5585 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2807 : Mem) (v_2806 : reg (bv 128)) => do
      v_12358 <- evaluateAddress v_2807;
      v_12359 <- load v_12358 8;
      setRegister (lhs.of_reg v_2806) (concat (expression.bv_nat 32 0) (concat (extract v_12359 0 32) (concat (expression.bv_nat 32 0) (extract v_12359 32 64))));
      pure ()
    pat_end
