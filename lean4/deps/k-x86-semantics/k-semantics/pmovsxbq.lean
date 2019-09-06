def pmovsxbq1 : instruction :=
  definst "pmovsxbq" $ do
    pattern fun (v_2766 : reg (bv 128)) (v_2767 : reg (bv 128)) => do
      v_5476 <- getRegister v_2766;
      setRegister (lhs.of_reg v_2767) (concat (sext (extract v_5476 112 120) 64) (sext (extract v_5476 120 128) 64));
      pure ()
    pat_end;
    pattern fun (v_2762 : Mem) (v_2763 : reg (bv 128)) => do
      v_12222 <- evaluateAddress v_2762;
      v_12223 <- load v_12222 2;
      setRegister (lhs.of_reg v_2763) (concat (sext (extract v_12223 0 8) 64) (sext (extract v_12223 8 16) 64));
      pure ()
    pat_end
