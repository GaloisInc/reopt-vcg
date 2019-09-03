def pmovzxwq1 : instruction :=
  definst "pmovzxwq" $ do
    pattern fun (v_2765 : reg (bv 128)) (v_2766 : reg (bv 128)) => do
      v_5671 <- getRegister v_2765;
      setRegister (lhs.of_reg v_2766) (concat (expression.bv_nat 48 0) (concat (extract v_5671 96 112) (concat (expression.bv_nat 48 0) (extract v_5671 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2760 : Mem) (v_2761 : reg (bv 128)) => do
      v_12937 <- evaluateAddress v_2760;
      v_12938 <- load v_12937 4;
      setRegister (lhs.of_reg v_2761) (concat (expression.bv_nat 48 0) (concat (extract v_12938 0 16) (concat (expression.bv_nat 48 0) (extract v_12938 16 32))));
      pure ()
    pat_end
