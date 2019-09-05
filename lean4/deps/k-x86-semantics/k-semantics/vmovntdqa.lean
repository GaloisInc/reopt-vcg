def vmovntdqa1 : instruction :=
  definst "vmovntdqa" $ do
    pattern fun (v_2965 : Mem) (v_2966 : reg (bv 128)) => do
      v_10202 <- evaluateAddress v_2965;
      v_10203 <- load v_10202 16;
      setRegister (lhs.of_reg v_2966) v_10203;
      pure ()
    pat_end;
    pattern fun (v_2969 : Mem) (v_2970 : reg (bv 256)) => do
      v_10205 <- evaluateAddress v_2969;
      v_10206 <- load v_10205 32;
      setRegister (lhs.of_reg v_2970) v_10206;
      pure ()
    pat_end
