def vbroadcastss1 : instruction :=
  definst "vbroadcastss" $ do
    pattern fun (v_2888 : reg (bv 128)) (v_2889 : reg (bv 128)) => do
      v_5542 <- getRegister v_2888;
      v_5543 <- eval (extract v_5542 96 128);
      setRegister (lhs.of_reg v_2889) (concat (concat (concat v_5543 v_5543) v_5543) v_5543);
      pure ()
    pat_end;
    pattern fun (v_2898 : reg (bv 128)) (v_2895 : reg (bv 256)) => do
      v_5552 <- getRegister v_2898;
      v_5553 <- eval (extract v_5552 96 128);
      setRegister (lhs.of_reg v_2895) (concat (concat (concat (concat (concat (concat (concat v_5553 v_5553) v_5553) v_5553) v_5553) v_5553) v_5553) v_5553);
      pure ()
    pat_end;
    pattern fun (v_2881 : Mem) (v_2884 : reg (bv 128)) => do
      v_9894 <- evaluateAddress v_2881;
      v_9895 <- load v_9894 4;
      setRegister (lhs.of_reg v_2884) (concat (concat (concat v_9895 v_9895) v_9895) v_9895);
      pure ()
    pat_end;
    pattern fun (v_2890 : Mem) (v_2891 : reg (bv 256)) => do
      v_9900 <- evaluateAddress v_2890;
      v_9901 <- load v_9900 4;
      setRegister (lhs.of_reg v_2891) (concat (concat (concat (concat (concat (concat (concat v_9901 v_9901) v_9901) v_9901) v_9901) v_9901) v_9901) v_9901);
      pure ()
    pat_end
