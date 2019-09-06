def pmuldq1 : instruction :=
  definst "pmuldq" $ do
    pattern fun (v_2865 : reg (bv 128)) (v_2866 : reg (bv 128)) => do
      v_5651 <- getRegister v_2866;
      v_5654 <- getRegister v_2865;
      setRegister (lhs.of_reg v_2866) (concat (mul (sext (extract v_5651 32 64) 64) (sext (extract v_5654 32 64) 64)) (mul (sext (extract v_5651 96 128) 64) (sext (extract v_5654 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (v_2861 : Mem) (v_2862 : reg (bv 128)) => do
      v_12364 <- getRegister v_2862;
      v_12367 <- evaluateAddress v_2861;
      v_12368 <- load v_12367 16;
      setRegister (lhs.of_reg v_2862) (concat (mul (sext (extract v_12364 32 64) 64) (sext (extract v_12368 32 64) 64)) (mul (sext (extract v_12364 96 128) 64) (sext (extract v_12368 96 128) 64)));
      pure ()
    pat_end
