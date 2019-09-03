def punpckhbw1 : instruction :=
  definst "punpckhbw" $ do
    pattern fun (v_3162 : reg (bv 128)) (v_3163 : reg (bv 128)) => do
      v_9045 <- getRegister v_3162;
      v_9047 <- getRegister v_3163;
      setRegister (lhs.of_reg v_3163) (concat (concat (extract v_9045 0 8) (extract v_9047 0 8)) (concat (concat (extract v_9045 8 16) (extract v_9047 8 16)) (concat (concat (extract v_9045 16 24) (extract v_9047 16 24)) (concat (concat (extract v_9045 24 32) (extract v_9047 24 32)) (concat (concat (extract v_9045 32 40) (extract v_9047 32 40)) (concat (concat (extract v_9045 40 48) (extract v_9047 40 48)) (concat (concat (extract v_9045 48 56) (extract v_9047 48 56)) (concat (extract v_9045 56 64) (extract v_9047 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_3157 : Mem) (v_3158 : reg (bv 128)) => do
      v_15935 <- evaluateAddress v_3157;
      v_15936 <- load v_15935 16;
      v_15938 <- getRegister v_3158;
      setRegister (lhs.of_reg v_3158) (concat (concat (extract v_15936 0 8) (extract v_15938 0 8)) (concat (concat (extract v_15936 8 16) (extract v_15938 8 16)) (concat (concat (extract v_15936 16 24) (extract v_15938 16 24)) (concat (concat (extract v_15936 24 32) (extract v_15938 24 32)) (concat (concat (extract v_15936 32 40) (extract v_15938 32 40)) (concat (concat (extract v_15936 40 48) (extract v_15938 40 48)) (concat (concat (extract v_15936 48 56) (extract v_15938 48 56)) (concat (extract v_15936 56 64) (extract v_15938 56 64)))))))));
      pure ()
    pat_end
