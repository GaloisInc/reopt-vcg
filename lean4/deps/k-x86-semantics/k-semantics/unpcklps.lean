def unpcklps1 : instruction :=
  definst "unpcklps" $ do
    pattern fun (v_2651 : reg (bv 128)) (v_2652 : reg (bv 128)) => do
      v_4797 <- getRegister v_2651;
      v_4799 <- getRegister v_2652;
      setRegister (lhs.of_reg v_2652) (concat (concat (concat (extract v_4797 64 96) (extract v_4799 64 96)) (extract v_4797 96 128)) (extract v_4799 96 128));
      pure ()
    pat_end;
    pattern fun (v_2644 : Mem) (v_2647 : reg (bv 128)) => do
      v_9110 <- evaluateAddress v_2644;
      v_9111 <- load v_9110 16;
      v_9113 <- getRegister v_2647;
      setRegister (lhs.of_reg v_2647) (concat (concat (concat (extract v_9111 64 96) (extract v_9113 64 96)) (extract v_9111 96 128)) (extract v_9113 96 128));
      pure ()
    pat_end
