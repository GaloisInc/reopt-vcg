def pmovzxwq1 : instruction :=
  definst "pmovzxwq" $ do
    pattern fun (v_2779 : reg (bv 128)) (v_2780 : reg (bv 128)) => do
      v_5582 <- getRegister v_2779;
      setRegister (lhs.of_reg v_2780) (concat (expression.bv_nat 48 0) (concat (extract v_5582 96 112) (concat (expression.bv_nat 48 0) (extract v_5582 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2775 : Mem) (v_2776 : reg (bv 128)) => do
      v_12522 <- evaluateAddress v_2775;
      v_12523 <- load v_12522 4;
      setRegister (lhs.of_reg v_2776) (concat (expression.bv_nat 48 0) (concat (extract v_12523 0 16) (concat (expression.bv_nat 48 0) (extract v_12523 16 32))));
      pure ()
    pat_end
