def orps1 : instruction :=
  definst "orps" $ do
    pattern fun (v_3075 : reg (bv 128)) (v_3076 : reg (bv 128)) => do
      v_4850 <- getRegister v_3076;
      v_4851 <- getRegister v_3075;
      setRegister (lhs.of_reg v_3076) (bv_or v_4850 v_4851);
      pure ()
    pat_end;
    pattern fun (v_3071 : Mem) (v_3072 : reg (bv 128)) => do
      v_9019 <- getRegister v_3072;
      v_9020 <- evaluateAddress v_3071;
      v_9021 <- load v_9020 16;
      setRegister (lhs.of_reg v_3072) (bv_or v_9019 v_9021);
      pure ()
    pat_end
