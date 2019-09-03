def punpckhwd1 : instruction :=
  definst "punpckhwd" $ do
    pattern fun (v_3189 : reg (bv 128)) (v_3190 : reg (bv 128)) => do
      v_9107 <- getRegister v_3189;
      v_9109 <- getRegister v_3190;
      setRegister (lhs.of_reg v_3190) (concat (concat (extract v_9107 0 16) (extract v_9109 0 16)) (concat (concat (extract v_9107 16 32) (extract v_9109 16 32)) (concat (concat (extract v_9107 32 48) (extract v_9109 32 48)) (concat (extract v_9107 48 64) (extract v_9109 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_3184 : Mem) (v_3185 : reg (bv 128)) => do
      v_15988 <- evaluateAddress v_3184;
      v_15989 <- load v_15988 16;
      v_15991 <- getRegister v_3185;
      setRegister (lhs.of_reg v_3185) (concat (concat (extract v_15989 0 16) (extract v_15991 0 16)) (concat (concat (extract v_15989 16 32) (extract v_15991 16 32)) (concat (concat (extract v_15989 32 48) (extract v_15991 32 48)) (concat (extract v_15989 48 64) (extract v_15991 48 64)))));
      pure ()
    pat_end
