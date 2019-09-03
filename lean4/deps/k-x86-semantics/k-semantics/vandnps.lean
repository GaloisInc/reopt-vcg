def vandnps1 : instruction :=
  definst "vandnps" $ do
    pattern fun (v_2694 : Mem) (v_2697 : reg (bv 128)) (v_2698 : reg (bv 128)) => do
      v_9596 <- getRegister v_2697;
      v_9600 <- evaluateAddress v_2694;
      v_9601 <- load v_9600 16;
      setRegister (lhs.of_reg v_2698) (bv_and (bv_xor v_9596 (mi (bitwidthMInt v_9596) -1)) v_9601);
      pure ()
    pat_end;
    pattern fun (v_2705 : Mem) (v_2706 : reg (bv 256)) (v_2707 : reg (bv 256)) => do
      v_9604 <- getRegister v_2706;
      v_9608 <- evaluateAddress v_2705;
      v_9609 <- load v_9608 32;
      setRegister (lhs.of_reg v_2707) (bv_and (bv_xor v_9604 (mi (bitwidthMInt v_9604) -1)) v_9609);
      pure ()
    pat_end
