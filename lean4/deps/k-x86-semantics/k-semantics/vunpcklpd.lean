def vunpcklpd1 : instruction :=
  definst "vunpcklpd" $ do
    pattern fun (v_3244 : reg (bv 128)) (v_3245 : reg (bv 128)) (v_3246 : reg (bv 128)) => do
      v_7580 <- getRegister v_3244;
      v_7582 <- getRegister v_3245;
      setRegister (lhs.of_reg v_3246) (concat (extract v_7580 64 128) (extract v_7582 64 128));
      pure ()
    pat_end;
    pattern fun (v_3255 : reg (bv 256)) (v_3256 : reg (bv 256)) (v_3257 : reg (bv 256)) => do
      v_7591 <- getRegister v_3255;
      v_7593 <- getRegister v_3256;
      setRegister (lhs.of_reg v_3257) (concat (concat (extract v_7591 64 128) (extract v_7593 64 128)) (concat (extract v_7591 192 256) (extract v_7593 192 256)));
      pure ()
    pat_end;
    pattern fun (v_3238 : Mem) (v_3239 : reg (bv 128)) (v_3240 : reg (bv 128)) => do
      v_13444 <- evaluateAddress v_3238;
      v_13445 <- load v_13444 16;
      v_13447 <- getRegister v_3239;
      setRegister (lhs.of_reg v_3240) (concat (extract v_13445 64 128) (extract v_13447 64 128));
      pure ()
    pat_end;
    pattern fun (v_3249 : Mem) (v_3250 : reg (bv 256)) (v_3251 : reg (bv 256)) => do
      v_13451 <- evaluateAddress v_3249;
      v_13452 <- load v_13451 32;
      v_13454 <- getRegister v_3250;
      setRegister (lhs.of_reg v_3251) (concat (concat (extract v_13452 64 128) (extract v_13454 64 128)) (concat (extract v_13452 192 256) (extract v_13454 192 256)));
      pure ()
    pat_end
