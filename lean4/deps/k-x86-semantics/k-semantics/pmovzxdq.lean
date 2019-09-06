def pmovzxdq1 : instruction :=
  definst "pmovzxdq" $ do
    pattern fun (v_2838 : reg (bv 128)) (v_2839 : reg (bv 128)) => do
      v_5612 <- getRegister v_2838;
      setRegister (lhs.of_reg v_2839) (concat (expression.bv_nat 32 0) (concat (extract v_5612 64 96) (concat (expression.bv_nat 32 0) (extract v_5612 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2834 : Mem) (v_2835 : reg (bv 128)) => do
      v_12334 <- evaluateAddress v_2834;
      v_12335 <- load v_12334 8;
      setRegister (lhs.of_reg v_2835) (concat (expression.bv_nat 32 0) (concat (extract v_12335 0 32) (concat (expression.bv_nat 32 0) (extract v_12335 32 64))));
      pure ()
    pat_end
