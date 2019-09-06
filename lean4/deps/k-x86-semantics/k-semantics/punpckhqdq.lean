def punpckhqdq1 : instruction :=
  definst "punpckhqdq" $ do
    pattern fun (v_3271 : reg (bv 128)) (v_3272 : reg (bv 128)) => do
      v_8738 <- getRegister v_3271;
      v_8740 <- getRegister v_3272;
      setRegister (lhs.of_reg v_3272) (concat (extract v_8738 0 64) (extract v_8740 0 64));
      pure ()
    pat_end;
    pattern fun (v_3267 : Mem) (v_3268 : reg (bv 128)) => do
      v_15135 <- evaluateAddress v_3267;
      v_15136 <- load v_15135 16;
      v_15138 <- getRegister v_3268;
      setRegister (lhs.of_reg v_3268) (concat (extract v_15136 0 64) (extract v_15138 0 64));
      pure ()
    pat_end
