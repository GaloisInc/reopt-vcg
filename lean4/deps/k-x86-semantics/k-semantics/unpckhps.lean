def unpckhps1 : instruction :=
  definst "unpckhps" $ do
    pattern fun (v_2542 : reg (bv 128)) (v_2543 : reg (bv 128)) => do
      v_4774 <- getRegister v_2542;
      v_4776 <- getRegister v_2543;
      setRegister (lhs.of_reg v_2543) (concat (concat (concat (extract v_4774 0 32) (extract v_4776 0 32)) (extract v_4774 32 64)) (extract v_4776 32 64));
      pure ()
    pat_end;
    pattern fun (v_2535 : Mem) (v_2538 : reg (bv 128)) => do
      v_9253 <- evaluateAddress v_2535;
      v_9254 <- load v_9253 16;
      v_9256 <- getRegister v_2538;
      setRegister (lhs.of_reg v_2538) (concat (concat (concat (extract v_9254 0 32) (extract v_9256 0 32)) (extract v_9254 32 64)) (extract v_9256 32 64));
      pure ()
    pat_end
