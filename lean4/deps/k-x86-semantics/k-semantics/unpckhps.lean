def unpckhps1 : instruction :=
  definst "unpckhps" $ do
    pattern fun (v_2633 : reg (bv 128)) (v_2634 : reg (bv 128)) => do
      v_4773 <- getRegister v_2633;
      v_4775 <- getRegister v_2634;
      setRegister (lhs.of_reg v_2634) (concat (concat (concat (extract v_4773 0 32) (extract v_4775 0 32)) (extract v_4773 32 64)) (extract v_4775 32 64));
      pure ()
    pat_end;
    pattern fun (v_2626 : Mem) (v_2629 : reg (bv 128)) => do
      v_9092 <- evaluateAddress v_2626;
      v_9093 <- load v_9092 16;
      v_9095 <- getRegister v_2629;
      setRegister (lhs.of_reg v_2629) (concat (concat (concat (extract v_9093 0 32) (extract v_9095 0 32)) (extract v_9093 32 64)) (extract v_9095 32 64));
      pure ()
    pat_end
