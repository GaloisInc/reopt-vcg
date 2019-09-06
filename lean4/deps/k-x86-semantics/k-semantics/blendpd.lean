def blendpd1 : instruction :=
  definst "blendpd" $ do
    pattern fun (v_3006 : imm int) (v_3004 : reg (bv 128)) (v_3005 : reg (bv 128)) => do
      v_5614 <- eval (handleImmediateWithSignExtend v_3006 8 8);
      v_5616 <- getRegister v_3005;
      v_5618 <- getRegister v_3004;
      setRegister (lhs.of_reg v_3005) (concat (mux (isBitClear v_5614 6) (extract v_5616 0 64) (extract v_5618 0 64)) (mux (isBitClear v_5614 7) (extract v_5616 64 128) (extract v_5618 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3000 : imm int) (v_3003 : Mem) (v_2999 : reg (bv 128)) => do
      v_9112 <- eval (handleImmediateWithSignExtend v_3000 8 8);
      v_9114 <- getRegister v_2999;
      v_9116 <- evaluateAddress v_3003;
      v_9117 <- load v_9116 16;
      setRegister (lhs.of_reg v_2999) (concat (mux (isBitClear v_9112 6) (extract v_9114 0 64) (extract v_9117 0 64)) (mux (isBitClear v_9112 7) (extract v_9114 64 128) (extract v_9117 64 128)));
      pure ()
    pat_end
