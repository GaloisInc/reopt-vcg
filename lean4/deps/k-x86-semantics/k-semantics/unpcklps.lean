def unpcklps1 : instruction :=
  definst "unpcklps" $ do
    pattern fun (v_2560 : reg (bv 128)) (v_2561 : reg (bv 128)) => do
      v_4798 <- getRegister v_2560;
      v_4800 <- getRegister v_2561;
      setRegister (lhs.of_reg v_2561) (concat (concat (concat (extract v_4798 64 96) (extract v_4800 64 96)) (extract v_4798 96 128)) (extract v_4800 96 128));
      pure ()
    pat_end;
    pattern fun (v_2553 : Mem) (v_2556 : reg (bv 128)) => do
      v_9271 <- evaluateAddress v_2553;
      v_9272 <- load v_9271 16;
      v_9274 <- getRegister v_2556;
      setRegister (lhs.of_reg v_2556) (concat (concat (concat (extract v_9272 64 96) (extract v_9274 64 96)) (extract v_9272 96 128)) (extract v_9274 96 128));
      pure ()
    pat_end
