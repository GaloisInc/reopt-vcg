def punpckhwd1 : instruction :=
  definst "punpckhwd" $ do
    pattern fun (v_3252 : reg (bv 128)) (v_3253 : reg (bv 128)) => do
      v_8721 <- getRegister v_3252;
      v_8723 <- getRegister v_3253;
      setRegister (lhs.of_reg v_3253) (concat (concat (extract v_8721 0 16) (extract v_8723 0 16)) (concat (concat (extract v_8721 16 32) (extract v_8723 16 32)) (concat (concat (extract v_8721 32 48) (extract v_8723 32 48)) (concat (extract v_8721 48 64) (extract v_8723 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_3249 : Mem) (v_3248 : reg (bv 128)) => do
      v_15166 <- evaluateAddress v_3249;
      v_15167 <- load v_15166 16;
      v_15169 <- getRegister v_3248;
      setRegister (lhs.of_reg v_3248) (concat (concat (extract v_15167 0 16) (extract v_15169 0 16)) (concat (concat (extract v_15167 16 32) (extract v_15169 16 32)) (concat (concat (extract v_15167 32 48) (extract v_15169 32 48)) (concat (extract v_15167 48 64) (extract v_15169 48 64)))));
      pure ()
    pat_end
