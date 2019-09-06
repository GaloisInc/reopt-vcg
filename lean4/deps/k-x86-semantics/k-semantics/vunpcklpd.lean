def vunpcklpd1 : instruction :=
  definst "vunpcklpd" $ do
    pattern fun (v_3271 : reg (bv 128)) (v_3272 : reg (bv 128)) (v_3273 : reg (bv 128)) => do
      v_7607 <- getRegister v_3271;
      v_7609 <- getRegister v_3272;
      setRegister (lhs.of_reg v_3273) (concat (extract v_7607 64 128) (extract v_7609 64 128));
      pure ()
    pat_end;
    pattern fun (v_3282 : reg (bv 256)) (v_3283 : reg (bv 256)) (v_3284 : reg (bv 256)) => do
      v_7618 <- getRegister v_3282;
      v_7620 <- getRegister v_3283;
      setRegister (lhs.of_reg v_3284) (concat (concat (extract v_7618 64 128) (extract v_7620 64 128)) (concat (extract v_7618 192 256) (extract v_7620 192 256)));
      pure ()
    pat_end;
    pattern fun (v_3265 : Mem) (v_3266 : reg (bv 128)) (v_3267 : reg (bv 128)) => do
      v_13471 <- evaluateAddress v_3265;
      v_13472 <- load v_13471 16;
      v_13474 <- getRegister v_3266;
      setRegister (lhs.of_reg v_3267) (concat (extract v_13472 64 128) (extract v_13474 64 128));
      pure ()
    pat_end;
    pattern fun (v_3276 : Mem) (v_3277 : reg (bv 256)) (v_3278 : reg (bv 256)) => do
      v_13478 <- evaluateAddress v_3276;
      v_13479 <- load v_13478 32;
      v_13481 <- getRegister v_3277;
      setRegister (lhs.of_reg v_3278) (concat (concat (extract v_13479 64 128) (extract v_13481 64 128)) (concat (extract v_13479 192 256) (extract v_13481 192 256)));
      pure ()
    pat_end
