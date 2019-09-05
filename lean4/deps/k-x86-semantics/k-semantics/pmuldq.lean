def pmuldq1 : instruction :=
  definst "pmuldq" $ do
    pattern fun (v_2837 : reg (bv 128)) (v_2838 : reg (bv 128)) => do
      v_5624 <- getRegister v_2838;
      v_5627 <- getRegister v_2837;
      setRegister (lhs.of_reg v_2838) (concat (mul (sext (extract v_5624 32 64) 64) (sext (extract v_5627 32 64) 64)) (mul (sext (extract v_5624 96 128) 64) (sext (extract v_5627 96 128) 64)));
      pure ()
    pat_end;
    pattern fun (v_2834 : Mem) (v_2833 : reg (bv 128)) => do
      v_12388 <- getRegister v_2833;
      v_12391 <- evaluateAddress v_2834;
      v_12392 <- load v_12391 16;
      setRegister (lhs.of_reg v_2833) (concat (mul (sext (extract v_12388 32 64) 64) (sext (extract v_12392 32 64) 64)) (mul (sext (extract v_12388 96 128) 64) (sext (extract v_12392 96 128) 64)));
      pure ()
    pat_end
