def andps1 : instruction :=
  definst "andps" $ do
    pattern fun (v_2920 : reg (bv 128)) (v_2921 : reg (bv 128)) => do
      v_5305 <- getRegister v_2921;
      v_5306 <- getRegister v_2920;
      setRegister (lhs.of_reg v_2921) (bv_and v_5305 v_5306);
      pure ()
    pat_end;
    pattern fun (v_2919 : Mem) (v_2916 : reg (bv 128)) => do
      v_9025 <- getRegister v_2916;
      v_9026 <- evaluateAddress v_2919;
      v_9027 <- load v_9026 16;
      setRegister (lhs.of_reg v_2916) (bv_and v_9025 v_9027);
      pure ()
    pat_end
