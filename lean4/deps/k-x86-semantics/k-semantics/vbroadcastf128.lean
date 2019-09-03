def vbroadcastf1281 : instruction :=
  definst "vbroadcastf128" $ do
    pattern fun (v_2877 : Mem) (v_2878 : reg (bv 256)) => do
      v_11422 <- evaluateAddress v_2877;
      v_11423 <- load v_11422 16;
      setRegister (lhs.of_reg v_2878) (concat v_11423 v_11423);
      pure ()
    pat_end
