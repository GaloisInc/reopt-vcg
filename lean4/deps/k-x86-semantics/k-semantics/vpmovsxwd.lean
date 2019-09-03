def vpmovsxwd1 : instruction :=
  definst "vpmovsxwd" $ do
    pattern fun (v_2675 : reg (bv 128)) (v_2676 : reg (bv 128)) => do
      v_5601 <- getRegister v_2675;
      setRegister (lhs.of_reg v_2676) (concat (leanSignExtend (extract v_5601 64 80) 32) (concat (leanSignExtend (extract v_5601 80 96) 32) (concat (leanSignExtend (extract v_5601 96 112) 32) (leanSignExtend (extract v_5601 112 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2684 : reg (bv 128)) (v_2686 : reg (bv 256)) => do
      v_5618 <- getRegister v_2684;
      setRegister (lhs.of_reg v_2686) (concat (leanSignExtend (extract v_5618 0 16) 32) (concat (leanSignExtend (extract v_5618 16 32) 32) (concat (leanSignExtend (extract v_5618 32 48) 32) (concat (leanSignExtend (extract v_5618 48 64) 32) (concat (leanSignExtend (extract v_5618 64 80) 32) (concat (leanSignExtend (extract v_5618 80 96) 32) (concat (leanSignExtend (extract v_5618 96 112) 32) (leanSignExtend (extract v_5618 112 128) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2670 : Mem) (v_2671 : reg (bv 128)) => do
      v_12264 <- evaluateAddress v_2670;
      v_12265 <- load v_12264 8;
      setRegister (lhs.of_reg v_2671) (concat (leanSignExtend (extract v_12265 0 16) 32) (concat (leanSignExtend (extract v_12265 16 32) 32) (concat (leanSignExtend (extract v_12265 32 48) 32) (leanSignExtend (extract v_12265 48 64) 32))));
      pure ()
    pat_end;
    pattern fun (v_2679 : Mem) (v_2681 : reg (bv 256)) => do
      v_12278 <- evaluateAddress v_2679;
      v_12279 <- load v_12278 16;
      setRegister (lhs.of_reg v_2681) (concat (leanSignExtend (extract v_12279 0 16) 32) (concat (leanSignExtend (extract v_12279 16 32) 32) (concat (leanSignExtend (extract v_12279 32 48) 32) (concat (leanSignExtend (extract v_12279 48 64) 32) (concat (leanSignExtend (extract v_12279 64 80) 32) (concat (leanSignExtend (extract v_12279 80 96) 32) (concat (leanSignExtend (extract v_12279 96 112) 32) (leanSignExtend (extract v_12279 112 128) 32))))))));
      pure ()
    pat_end
