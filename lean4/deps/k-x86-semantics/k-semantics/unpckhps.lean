def unpckhps1 : instruction :=
  definst "unpckhps" $ do
    pattern fun (v_2606 : reg (bv 128)) (v_2607 : reg (bv 128)) => do
      v_4746 <- getRegister v_2606;
      v_4748 <- getRegister v_2607;
      setRegister (lhs.of_reg v_2607) (concat (concat (concat (extract v_4746 0 32) (extract v_4748 0 32)) (extract v_4746 32 64)) (extract v_4748 32 64));
      pure ()
    pat_end;
    pattern fun (v_2601 : Mem) (v_2602 : reg (bv 128)) => do
      v_9065 <- evaluateAddress v_2601;
      v_9066 <- load v_9065 16;
      v_9068 <- getRegister v_2602;
      setRegister (lhs.of_reg v_2602) (concat (concat (concat (extract v_9066 0 32) (extract v_9068 0 32)) (extract v_9066 32 64)) (extract v_9068 32 64));
      pure ()
    pat_end
