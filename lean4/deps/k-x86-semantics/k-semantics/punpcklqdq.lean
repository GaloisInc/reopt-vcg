def punpcklqdq1 : instruction :=
  definst "punpcklqdq" $ do
    pattern fun (v_3216 : reg (bv 128)) (v_3217 : reg (bv 128)) => do
      v_9181 <- getRegister v_3216;
      v_9183 <- getRegister v_3217;
      setRegister (lhs.of_reg v_3217) (concat (extract v_9181 64 128) (extract v_9183 64 128));
      pure ()
    pat_end;
    pattern fun (v_3211 : Mem) (v_3212 : reg (bv 128)) => do
      v_16053 <- evaluateAddress v_3211;
      v_16054 <- load v_16053 16;
      v_16056 <- getRegister v_3212;
      setRegister (lhs.of_reg v_3212) (concat (extract v_16054 64 128) (extract v_16056 64 128));
      pure ()
    pat_end
