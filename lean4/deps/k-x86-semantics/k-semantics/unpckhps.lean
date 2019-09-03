def unpckhps1 : instruction :=
  definst "unpckhps" $ do
    pattern fun (v_2555 : reg (bv 128)) (v_2556 : reg (bv 128)) => do
      v_4785 <- getRegister v_2555;
      v_4787 <- getRegister v_2556;
      setRegister (lhs.of_reg v_2556) (concat (concat (concat (extract v_4785 0 32) (extract v_4787 0 32)) (extract v_4785 32 64)) (extract v_4787 32 64));
      pure ()
    pat_end;
    pattern fun (v_2548 : Mem) (v_2551 : reg (bv 128)) => do
      v_10347 <- evaluateAddress v_2548;
      v_10348 <- load v_10347 16;
      v_10350 <- getRegister v_2551;
      setRegister (lhs.of_reg v_2551) (concat (concat (concat (extract v_10348 0 32) (extract v_10350 0 32)) (extract v_10348 32 64)) (extract v_10350 32 64));
      pure ()
    pat_end
