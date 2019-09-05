def unpcklps1 : instruction :=
  definst "unpcklps" $ do
    pattern fun (v_2624 : reg (bv 128)) (v_2625 : reg (bv 128)) => do
      v_4770 <- getRegister v_2624;
      v_4772 <- getRegister v_2625;
      setRegister (lhs.of_reg v_2625) (concat (concat (concat (extract v_4770 64 96) (extract v_4772 64 96)) (extract v_4770 96 128)) (extract v_4772 96 128));
      pure ()
    pat_end;
    pattern fun (v_2619 : Mem) (v_2620 : reg (bv 128)) => do
      v_9083 <- evaluateAddress v_2619;
      v_9084 <- load v_9083 16;
      v_9086 <- getRegister v_2620;
      setRegister (lhs.of_reg v_2620) (concat (concat (concat (extract v_9084 64 96) (extract v_9086 64 96)) (extract v_9084 96 128)) (extract v_9086 96 128));
      pure ()
    pat_end
